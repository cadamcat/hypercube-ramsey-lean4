import HypercubeRamsey.S06.OddLoads
import HypercubeRamsey.S06.EvenRows_sol_s06_joint
import HypercubeRamsey.S06.Prob
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.S06.EvenRows_q_s06_even
import HypercubeRamsey.S06.EvenRows_q_s06_ev_b
import HypercubeRamsey.S06.EvenRows_sol_s06_ev_b
import HypercubeRamsey.S06.EvenRows_select_sol_s06_ev_b
import HypercubeRamsey.S06.EvenRows_q_s06_ev_d
import HypercubeRamsey.S06.EvenRows_sol_s06_ev_d
import HypercubeRamsey.S06.EvenRows_q_s06_ev_a

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

/-- Auxiliary odd sampling uses a probability filler on an invalid row. -/
def oddLaw (H : X.Hist) (C : X.Centre) (u : CubeVertex n) : Law N :=
  if X.OddValid H C X.Rlong (X.g.L.stateOf u) then
    match X.stMode (X.g.L.stateOf u) with
    | .low => X.lowRow H (X.pos C) (X.g.L.stateOf u)
        (X.actDesc H C X.Rlong (X.g.L.stateOf u)) (X.tup C)
    | .high => X.s3Post H (X.g.L.stateOf u)
        (X.actDesc H C X.Rlong (X.g.L.stateOf u)) (X.tup C)
  else X.unifLaw

theorem oddLaw_eq_row (H : X.Hist) (C : X.Centre) (u : CubeVertex n)
    (hu : X.OddValid H C X.Rlong (X.g.L.stateOf u)) (a : Fin N) :
    (X.oddLaw H C u).w a = X.oddRow H C u a := by
  unfold oddLaw Ctx6.oddRow Ctx6.oddRowAt
  rw [if_pos hu, if_pos hu]
  cases X.stMode (X.g.L.stateOf u) <;> rfl

/-- The normalized local even-row mean under auxiliary product odd sampling with probability fillers
on invalid rows (06:836–838). The even row retains its own local gate. -/
def localEvenMean (H : X.Hist) (C : X.Centre) (v : CubeVertex n) (a : Fin N) : ℝ :=
  (FinProb.pi (fun u : OddRole6 n => X.oddLaw H C u.1)).expect
    (fun y => (N : ℝ) * X.evenRow H C v y a)

/-- Product of the zero-extended odd rows; globally gated by `AllOddValid`. -/
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
    (X.centreLaw H).expect (fun C => X.localEvenMean H C v a) ≤
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

private theorem evenTy_occ (X : Ctx6 γ p₀ K n N E G M) (v : CubeVertex n)
    (hv : IsEvenRole v) : X.evenTy v ∈ X.occTypes := by
  have heq : X.evenTy v = X.evenType v := by
    simp only [Ctx6.evenTy, Ctx6.stType, ChunkLayout6.stType, Ctx6.evenType,
      X.facts.key_eq, X.facts.sign_eq, X.facts.flippable_eq, X.facts.severity_eq]
  rw [heq]
  exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩

private theorem baseSupp_keys (X : Ctx6 γ p₀ K n N E G M) (H : X.Hist)
    (hb : X.BaseSupp H.1) (S : Finset X.Key) : X.KeysSupp H.1 S := by
  refine ⟨hb.1, ?_, ?_⟩
  · intro u hu
    exact hb.2.1 u (Finset.mem_image.mpr ⟨⟨u, .interior⟩, Finset.mem_univ _, rfl⟩)
  · intro s hs
    exact hb.2.2 s (Finset.mem_univ _)

private theorem Fz_nonneg (X : Ctx6 γ p₀ K n N E G M) (hrow : X.OddRowBounds)
    (H : X.Hist) (hH : X.histLaw.w H ≠ 0) (C : X.Centre) (v : CubeVertex n)
    (c : X.Loc) (z : X.Tuple) (y : OddRole6 n → Fin N) : 0 ≤ X.Fz H C v c z y := by
  unfold Ctx6.Fz
  split_ifs with hg
  · simp only [one_mul]
    exact Finset.prod_nonneg fun u hu => (hrow H _ u.1 hH u.2 (hg.2.2.1 u hu)).1 (y u)
  · simp

private theorem Fz_hits (X : Ctx6 γ p₀ K n N E G M) (hrow : X.OddRowBounds)
    (H : X.Hist) (hH : X.histLaw.w H ≠ 0) (C : X.Centre) (v : CubeVertex n)
    (hv : IsEvenRole v) (c : X.Loc) (z : X.Tuple) (y : OddRole6 n → Fin N)
    (hF : X.Fz H C v c z y ≠ 0) :
    ∀ u ∈ X.oddNbrs v, ∀ r, Hits E G (z.2 r) (y u) := by
  have hg : X.EvenGate H (X.withTuple C (c, X.evenTy v) z) v c := by
    by_contra h
    simp [Ctx6.Fz, h] at hF
  have hprod : (∏ u ∈ X.oddNbrs v,
      X.oddRow H (X.withTuple C (c, X.evenTy v) z) u.1 (y u)) ≠ 0 := by
    simpa [Ctx6.Fz, hg] using hF
  intro u hu r
  have hnonzero := (Finset.prod_ne_zero_iff.mp hprod) u hu
  have hpair := Lane_q_s06_even.selected_pair_mem_actDesc X H
    (X.withTuple C (c, X.evenTy v) z) v u.1 hv u.2
    (SimpleGraph.Adj.symm (Finset.mem_filter.mp hu).2)
  have hpair' : (c, X.evenTy v) ∈
      X.actDesc H (X.withTuple C (c, X.evenTy v) z) X.Rlong (X.g.L.stateOf u.1) := by
    change ((X.choice H (X.withTuple C (c, X.evenTy v) z) X.Rlong (X.g.L.stateOf v)).getD X.defaultLoc,
      X.evenTy v) ∈ _ at hpair
    simpa only [hg.1, Option.getD_some] using hpair
  have hh := (hrow H _ u.1 hH u.2 (hg.2.2.1 u hu)).2.2.2.1
    (y u) hnonzero (c, X.evenTy v) hpair' r
  simpa [Ctx6.withTuple, Ctx6.tup] using hh

private theorem even_k_pos (X : Ctx6 γ p₀ K n N E G M) (hn : 2 ≤ n) : 0 < X.k := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hm : 0 < X.g.L.m := by
    rw [X.g.m_eq]
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)
  have hmR : (1 : ℝ) ≤ X.g.L.m := by exact_mod_cast hm
  have hJ : (1 : ℝ) ≤ (X.J : ℝ) := by
    have hp : (1 : ℝ) ≤ (X.g.L.m : ℝ) ^ (1 / 25 : ℝ) := Real.one_le_rpow hmR (by norm_num)
    have h : 1 ≤ J₆ X.g.L.m := by
      unfold J₆
      exact (Nat.le_floor_iff (by positivity)).mpr (by simpa using hp)
    exact_mod_cast h
  unfold Ctx6.k k₆
  apply Nat.ceil_pos.mpr
  have : 0 < κ₆ := by norm_num [κ₆]
  have : 0 < (J₆ X.g.L.m : ℝ) := by change 0 < (X.J : ℝ); linarith
  exact mul_pos (mul_pos (by norm_num [κ₆]) this) (Real.log_pos hnR)

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

set_option maxHeartbeats 50000000
/-- L6.1m (domination, 06:787–811): at a matching neighbour `p_b ≤ e^{.2k}|𝒟_{b,c}| q_b` with
`log|𝒟_{b,c}| < .1k`; the `o(n^{.4})` other neighbours (coarse or fine chunk flips) cost `o(kn)`. -/
theorem L6_1m_dom (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.OddRowBounds → X.DescCount → X.EvenDom := by
  have hp₀ : 0 < p₀ := hadm.2.2.1
  obtain ⟨nGrowth, hGrowth⟩ := Lane_q_s06_ev_a.parameter_growth p₀ hp₀
  obtain ⟨nScale, hScale⟩ := Lane_q_s06_ev_a.topScale_fourth_eventually p₀ hp₀
  refine ⟨max nGrowth nScale, 1, ?_⟩
  intro n N E G M X hL hRows hDesc H C v z y hH hv
  classical
  have hGrowthN := hGrowth n (le_trans (le_max_left _ _) hL.1)
  rcases hGrowthN with ⟨hJgrowth, hTgrowth, hlogTgrowth, hmGrowth, hkGrowth, hnGrowth⟩
  have hScaleN := hScale n (le_trans (le_max_right _ _) hL.1)
  have hαfacts := height_exponents6_admissible p₀ hp₀
  have hαzero : 0 ≤ α₆ p₀ := hαfacts.1.le
  have hαbound : α₆ p₀ ≤ 1 / 10 ^ 12 := hαfacts.2.2.1
  have hJlarge : 2000000 ≤ X.J := by
    simpa [Ctx6.J, Ctx6.m, X.g.m_eq, J₆, m₆] using hJgrowth
  have hTsmall : (X.T : ℝ) ≤ (1 / 10 ^ 11 : ℝ) * X.J := by
    simpa [Ctx6.T, Ctx6.J, Ctx6.m, X.g.m_eq, T₆, J₆, m₆] using hTgrowth
  have hlogT : Real.log (X.T + 2) ≤ 2 * α₆ p₀ * Real.log n := by
    simpa [Ctx6.T, Ctx6.m, X.g.m_eq, T₆, m₆] using hlogTgrowth
  have hmle : X.m ≤ n := by simpa [Ctx6.m, X.g.m_eq, m₆] using hmGrowth
  have hklarge : 12 ≤ X.k := by
    simpa [Ctx6.k, Ctx6.m, X.g.m_eq, k₆, J₆, m₆] using hkGrowth
  have hnlarge : 10 ^ 10 ≤ n := hnGrowth
  have hHscale : X.hp.H ≤ n ^ 4 := by
    simpa [Ctx6.hp, σ₆, ζ₆, α₆] using hScaleN
  have hkceil : κ₆ * (X.J : ℝ) * Real.log n ≤ (X.k : ℝ) := by
    dsimp [Ctx6.k, k₆]
    exact Nat.le_ceil _
  have hfamilyRate : (X.hp.H : ℝ) * Real.exp (10 ^ 4 *
      (X.T * Real.log (3 * n * (4 * n ^ 10) + 2) +
        (X.J + 1) * Real.log (X.T + 2))) ≤ Real.exp ((5 / 100 : ℝ) * X.k) := by
    exact Lane_q_s06_ev_a.family_rate_of_growth (n := n) (m := X.m) (J := X.J) (T := X.T)
      (H := X.hp.H) (k := X.k) (α := α₆ p₀) (by omega) hJlarge hTsmall hlogT hHscale
      hkceil hαzero hαbound
  let c := X.selC H C v
  let β := X.evenTy v
  let Cz := X.withTuple C (c, β) z
  by_cases hgate : X.EvenGate H Cz v c
  · have hN : 0 < N := by
      have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
        calc
          1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
          _ ≤ (N : ℝ) := by simpa using hL.2.1
      have hNnat : 1 ≤ N := by exact_mod_cast hNreal
      omega
    have hdim : 0 < n := by omega
    have hodd (u : OddRole6 n) (hu : u ∈ X.oddNbrs v) :
        X.OddValid H Cz X.Rlong (X.g.L.stateOf u.1) := by
      exact hgate.2.2.1 u hu
    have hβEq : X.evenTy v = X.evenType v := by
      simp [Ctx6.evenTy, Ctx6.evenType, Ctx6.stType, ChunkLayout6.stType,
        X.facts.key_eq v, X.facts.sign_eq v, X.facts.flippable_eq v, X.facts.severity_eq v]
    have hdescBound : ∀ (u : OddRole6 n), u ∈ X.oddNbrs v → ∀ c₀ : X.Loc × X.Ty,
        ((X.descsWith H Cz (X.g.L.stateOf u.1) c₀).card : ℝ) ≤
          (X.hp.H : ℝ) * Real.exp (10 ^ 4 *
            (X.T * Real.log (3 * n * (4 * n ^ 10) + 2) +
              (X.J + 1) * Real.log (X.T + 2))) := by
      intro u hu c₀
      let b := X.g.L.stateOf u.1
      have hvalid := hodd u hu
      have hbOdd : b ∈ X.g.L.oddStates := by
        apply Finset.mem_image.mpr
        exact ⟨u.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2⟩, rfl⟩
      have hperm : ∀ j : Fin X.hp.H, ∀ a : X.g.L.stNbr b,
          (X.permAt (X.pos Cz) b j a).card ≤ 4 * n ^ 10 := by
        intro j a
        have hbi : ((X.permAt (X.pos Cz) b j a).card : ℝ) ≤
            ∑ l ∈ X.levelPair j,
              ((X.prosp (X.pos Cz) (X.site a.1) l).card : ℝ) := by
          dsimp [Ctx6.permAt]
          exact_mod_cast Finset.card_biUnion_le
        have hlevels : ∀ l ∈ X.levelPair j,
            ((X.prosp (X.pos Cz) (X.site a.1) l).card : ℝ) ≤ 2 * X.hp.lam :=
          fun l hl => hvalid.2.1 a.1 a.2 l
        have hpaircard : (X.levelPair j).card ≤ 2 := by
          simpa [Ctx6.levelPair] using Finset.card_le_two
        have hlam : X.hp.lam = (n : ℝ) ^ 10 := by simp [Ctx6.hp, J₀₆]
        have hreal : ((X.permAt (X.pos Cz) b j a).card : ℝ) ≤
            4 * (n : ℝ) ^ 10 := by
          calc
            _ ≤ ∑ l ∈ X.levelPair j,
                  ((X.prosp (X.pos Cz) (X.site a.1) l).card : ℝ) := hbi
            _ ≤ ∑ _l ∈ X.levelPair j, 2 * X.hp.lam := by
                  apply Finset.sum_le_sum
                  intro l hl
                  exact hlevels l hl
            _ = ((X.levelPair j).card : ℝ) * (2 * X.hp.lam) := by simp
            _ ≤ 2 * (2 * X.hp.lam) := by
                  have hpaircardR : ((X.levelPair j).card : ℝ) ≤ 2 := by exact_mod_cast hpaircard
                  have hnonneg : 0 ≤ 2 * X.hp.lam := by rw [hlam]; positivity
                  nlinarith [mul_le_mul_of_nonneg_right hpaircardR hnonneg]
            _ = 4 * (n : ℝ) ^ 10 := by rw [hlam]; ring
        exact_mod_cast hreal
      have hcount (j : Fin X.hp.H) :
          ((X.descsIn b (X.permAt (X.pos Cz) b j)).card : ℝ) ≤
            Real.exp (10 ^ 4 *
              (X.T * Real.log (3 * n * (4 * n ^ 10) + 2) +
                (X.J + 1) * Real.log (X.T + 2))) := by
        simpa [Nat.cast_mul, Nat.cast_pow] using
          hDesc X.Loc b (X.permAt (X.pos Cz) b j) (4 * n ^ 10) hbOdd (hperm j)
      dsimp [Ctx6.descsWith]
      calc
        _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin X.hp.H)),
              (((X.descsIn b (X.permAt (X.pos Cz) b j)).filter
                (fun D => c₀ ∈ D)).card : ℝ) := by
              exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin X.hp.H)),
              Real.exp (10 ^ 4 *
                (X.T * Real.log (3 * n * (4 * n ^ 10) + 2) +
                  (X.J + 1) * Real.log (X.T + 2))) := by
              apply Finset.sum_le_sum
              intro j hj
              have hfilter :
                  (((X.descsIn b (X.permAt (X.pos Cz) b j)).filter
                    (fun D => c₀ ∈ D)).card : ℝ) ≤
                    ((X.descsIn b (X.permAt (X.pos Cz) b j)).card : ℝ) := by
                exact_mod_cast Finset.card_filter_le _ _
              exact hfilter.trans (hcount j)
        _ = (X.hp.H : ℝ) * Real.exp (10 ^ 4 *
              (X.T * Real.log (3 * n * (4 * n ^ 10) + 2) +
                (X.J + 1) * Real.log (X.T + 2))) := by simp
    have hrowCompare : ∀ u : OddRole6 n, u ∈ X.oddNbrs v →
        (if X.Matching (X.g.L.stateOf u.1) β then
          X.oddRow H Cz u.1 (y u) ≤ Real.exp ((25 / 100 : ℝ) * X.k) *
            (X.qRef H Cz v u).w (y u)
        else
          X.oddRow H Cz u.1 (y u) ≤
            (if X.stMode (X.g.L.stateOf u.1) = .low then
              Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ))
             else (n : ℝ) ^ ((5 / 100 : ℝ) * X.J)) *
              (X.qRef H Cz v u).w (y u)) := by
      intro u hu
      let b := X.g.L.stateOf u.1
      let D := X.actDesc H Cz X.Rlong b
      have hbvalid := hodd u hu
      have hbound := hRows H Cz u.1 hH u.2 hbvalid
      by_cases hmatch : X.Matching b β
      · have hadj : (cube n).Adj u.1 v := by
          exact (cube n).adj_symm ((Finset.mem_filter.mp hu).2)
        have hcchoice : X.choice H Cz X.Rlong (X.g.L.stateOf v) = some c := by
          exact hgate.1
        have hselCz : X.selC H Cz v = c := by
          simp [Ctx6.selC, hcchoice]
        obtain ⟨j, hD, hcD⟩ :=
          Lane_q_s06_even.selected_pair_in_descsIn_of_valid_neighbor
            X H Cz v u.1 hv u.2 hadj c hcchoice hbvalid
        have hcD' : (c, β) ∈ D := by
          simpa [D, b, β, Ctx6.evenTy, Ctx6.stType] using hcD
        have hmemFam : D ∈ X.descsWith H Cz b (c, β) := by
          apply Finset.mem_biUnion.mpr
          refine ⟨j, Finset.mem_univ _, ?_⟩
          exact Finset.mem_filter.mpr ⟨hD, hcD'⟩
        have hFamNe : (X.descsWith H Cz b (c, β)).Nonempty := ⟨D, hmemFam⟩
        have hFamNeQ :
            (X.descsWith H Cz b (X.selC H C v, X.evenType v)).Nonempty := by
          simpa [c, β, hβEq] using hFamNe
        have hFamBound := hdescBound u hu (c, β)
        have hdel := Lane_q_s06_even.law_le_card_normalized_sum
          (fun D' : Finset (X.Loc × X.Ty) => X.s3Del H b D' (X.tup Cz) (c, β))
          (X.descsWith H Cz b (c, β)) hFamNe D hmemFam X.y₀ (y u)
        have hqcond : X.Matching (X.g.L.stateOf u.1) (X.evenType v) ∧
            (X.descsWith H Cz (X.g.L.stateOf u.1)
              (X.selC H Cz v, X.evenType v)).Nonempty := by
          simpa [b, β, hβEq, hselCz] using And.intro hmatch hFamNe
        have hqref : (X.qRef H Cz v u).w (y u) =
            (normalize6 (fun y' =>
              ∑ D' ∈ X.descsWith H Cz b (c, β),
                (X.s3Del H b D' (X.tup Cz) (c, β)).w y') X.y₀).w (y u) := by
          have hcond' : X.Matching (X.g.L.stateOf u.1) (X.evenTy v) ∧
              (X.descsWith H Cz (X.g.L.stateOf u.1)
                (X.selC H Cz v, X.evenTy v)).Nonempty := by
            simpa [b, β, hselCz] using And.intro hmatch hFamNe
          unfold Ctx6.qRef
          dsimp only
          rw [if_pos hcond']
          simpa [b, c, β, hselCz]
        have hrowDel := hbound.2.2.2.2 (c, β) hcD' hmatch (y u)
        have hFamSmall : (X.descsWith H Cz b (c, β)).card ≤
            Real.exp ((5 / 100 : ℝ) * X.k) := by
          exact le_trans hFamBound hfamilyRate
        have hmatch' : X.Matching (X.g.L.stateOf u.1) β := by simpa [b] using hmatch
        try simp only [if_pos hmatch']
        rw [hqref]
        change X.oddRow H Cz u.1 (y u) ≤
          Real.exp ((25 / 100 : ℝ) * X.k) *
              (normalize6 (fun y' =>
                ∑ D' ∈ X.descsWith H Cz b (c, β),
                  (X.s3Del H b D' (X.tup Cz) (c, β)).w y') X.y₀).w (y u)
        calc
          X.oddRow H Cz u.1 (y u) ≤
              Real.exp ((2 / 10) * X.k) * (X.s3Del H b D (X.tup Cz) (c, β)).w (y u) :=
                hrowDel
          _ ≤ Real.exp ((2 / 10) * X.k) *
                ((X.descsWith H Cz b (c, β)).card : ℝ) *
                  (normalize6 (fun y' =>
                    ∑ D' ∈ X.descsWith H Cz b (c, β),
                      (X.s3Del H b D' (X.tup Cz) (c, β)).w y') X.y₀).w (y u) := by
                have hqnonneg :=
                  (normalize6 (fun y' =>
                    ∑ D' ∈ X.descsWith H Cz b (c, β),
                      (X.s3Del H b D' (X.tup Cz) (c, β)).w y') X.y₀).nonneg (y u)
                calc
                  _ = Real.exp ((2 / 10) * X.k) *
                      (X.s3Del H b D (X.tup Cz) (c, β)).w (y u) := by ring
                  _ ≤ Real.exp ((2 / 10) * X.k) *
                      (((X.descsWith H Cz b (c, β)).card : ℝ) *
                        (normalize6 (fun y' =>
                          ∑ D' ∈ X.descsWith H Cz b (c, β),
                            (X.s3Del H b D' (X.tup Cz) (c, β)).w y') X.y₀).w (y u)) :=
                    mul_le_mul_of_nonneg_left hdel (Real.exp_nonneg _)
                  _ = _ := by ring
          _ ≤ Real.exp ((2 / 10) * X.k) *
                (Real.exp ((5 / 100 : ℝ) * X.k) *
                  (normalize6 (fun y' =>
                    ∑ D' ∈ X.descsWith H Cz b (c, β),
                      (X.s3Del H b D' (X.tup Cz) (c, β)).w y') X.y₀).w (y u)) := by
                have hqnonneg :=
                  (normalize6 (fun y' =>
                    ∑ D' ∈ X.descsWith H Cz b (c, β),
                      (X.s3Del H b D' (X.tup Cz) (c, β)).w y') X.y₀).nonneg (y u)
                calc
                  _ = Real.exp ((2 / 10) * X.k) *
                      (((X.descsWith H Cz b (c, β)).card : ℝ) *
                        (normalize6 (fun y' =>
                          ∑ D' ∈ X.descsWith H Cz b (c, β),
                            (X.s3Del H b D' (X.tup Cz) (c, β)).w y') X.y₀).w (y u)) := by ring
                  _ ≤ Real.exp ((2 / 10) * X.k) *
                      (Real.exp ((5 / 100 : ℝ) * X.k) *
                        (normalize6 (fun y' =>
                          ∑ D' ∈ X.descsWith H Cz b (c, β),
                            (X.s3Del H b D' (X.tup Cz) (c, β)).w y') X.y₀).w (y u)) := by
                    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
                    exact mul_le_mul_of_nonneg_right hFamSmall hqnonneg
          _ = Real.exp ((25 / 100 : ℝ) * X.k) *
                (normalize6 (fun y' =>
                  ∑ D' ∈ X.descsWith H Cz b (c, β),
                    (X.s3Del H b D' (X.tup Cz) (c, β)).w y') X.y₀).w (y u) := by
                rw [← mul_assoc, ← Real.exp_add]
                congr 1
                ring
      · have hcap := hbound.2.2.1 (y u)
        have hmatch' : ¬ X.Matching (X.g.L.stateOf u.1) β := by simpa [b] using hmatch
        try simp only [if_neg hmatch']
        have hquniform : (X.qRef H Cz v u).w (y u) = (N : ℝ)⁻¹ := by
          unfold Ctx6.qRef
          dsimp only
          have hcond : ¬ (X.Matching (X.g.L.stateOf u.1) (X.evenTy v) ∧
              (X.descsWith H Cz (X.g.L.stateOf u.1)
                (X.selC H Cz v, X.evenTy v)).Nonempty) := by
            intro h
            exact hmatch' (by simpa [b, β] using h.1)
          rw [if_neg hcond]
          simp [Ctx6.unifLaw, normalize6, hN]
        rw [hquniform]
        have hcap' : (N : ℝ) * X.oddRow H Cz u.1 (y u) ≤
            (if X.stMode b = .low then Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ))
             else (n : ℝ) ^ ((5 / 100 : ℝ) * X.J)) := hcap
        rw [show b = X.g.L.stateOf u.1 from rfl] at hcap'
        have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
        have hrow_le : X.oddRow H Cz u.1 (y u) ≤
            (if X.stMode b = .low then Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ))
             else (n : ℝ) ^ ((5 / 100 : ℝ) * X.J)) / (N : ℝ) := by
          apply (le_div_iff₀ hNpos).2
          nlinarith [hcap']
        simpa [div_eq_mul_inv, hquniform] using hrow_le
    have hqRefEq : ∀ u : OddRole6 n, u ∈ X.oddNbrs v →
        (X.qRef H Cz v u).w (y u) = (X.qRef H C v u).w (y u) := by
      intro u hu
      let b := X.g.L.stateOf u.1
      by_cases hmatch : X.Matching b β
      · have hbvalid := hodd u hu
        have hcchoice : X.choice H Cz X.Rlong (X.g.L.stateOf v) = some c := hgate.1
        have hselCz : X.selC H Cz v = c := by simp [Ctx6.selC, hcchoice]
        have hselC : X.selC H C v = c := by rfl
        obtain ⟨j, hD, hcD⟩ :=
          Lane_q_s06_even.selected_pair_in_descsIn_of_valid_neighbor
            X H Cz v u.1 hv u.2 ((cube n).adj_symm ((Finset.mem_filter.mp hu).2))
            c hcchoice hbvalid
        let D := X.actDesc H Cz X.Rlong b
        have hcD' : (c, β) ∈ D := by
          simpa [D, b, β, Ctx6.evenTy, Ctx6.stType, ChunkLayout6.stType] using hcD
        have hFamNeZ : (X.descsWith H Cz b (c, β)).Nonempty := by
          refine ⟨D, ?_⟩
          apply Finset.mem_biUnion.mpr
          exact ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hD, hcD'⟩⟩
        have hFamEq : X.descsWith H Cz b (c, β) = X.descsWith H C b (c, β) := by
          rfl
        have hFamNeC : (X.descsWith H C b (c, β)).Nonempty := by
          rw [← hFamEq]
          exact hFamNeZ
        have hFamNeQC :
            (X.descsWith H C b (X.selC H C v, X.evenType v)).Nonempty := by
          simpa [c, β, hβEq] using hFamNeC
        have hDelEq (D' : Finset (X.Loc × X.Ty)) :
            X.s3Del H b D' (X.tup Cz) (c, β) = X.s3Del H b D' (X.tup C) (c, β) := by
          have htu : X.tup Cz = Function.update (X.tup C) (c, β) z := rfl
          rw [htu]
          exact Lane_q_s06_ev_a.s3Del_update_irrelevant X H b D' (X.tup C) (c, β) z
        have hsumEq : ∀ a,
            (∑ D' ∈ X.descsWith H Cz b (c, β),
              (X.s3Del H b D' (X.tup Cz) (c, β)).w a) =
            ∑ D' ∈ X.descsWith H C b (c, β),
              (X.s3Del H b D' (X.tup C) (c, β)).w a := by
          intro a
          rw [hFamEq]
          simp_rw [hDelEq]
        have hnormEq :
            normalize6 (fun a => ∑ D' ∈ X.descsWith H Cz b (c, β),
              (X.s3Del H b D' (X.tup Cz) (c, β)).w a) X.y₀ =
            normalize6 (fun a => ∑ D' ∈ X.descsWith H C b (c, β),
              (X.s3Del H b D' (X.tup C) (c, β)).w a) X.y₀ := by
          apply congrArg (fun f => normalize6 f X.y₀)
          funext a
          exact hsumEq a
        have hqcondZ : X.Matching (X.g.L.stateOf u.1) (X.evenType v) ∧
            (X.descsWith H Cz (X.g.L.stateOf u.1)
              (X.selC H Cz v, X.evenType v)).Nonempty := by
          simpa [b, β, hβEq, hselCz] using And.intro hmatch hFamNeZ
        have hqcondC : X.Matching (X.g.L.stateOf u.1) (X.evenType v) ∧
            (X.descsWith H C (X.g.L.stateOf u.1)
              (X.selC H C v, X.evenType v)).Nonempty := by
          simpa [b, β, hβEq, hselC] using And.intro hmatch hFamNeC
        have hqZ : (X.qRef H Cz v u).w (y u) =
            (normalize6 (fun a => ∑ D' ∈ X.descsWith H Cz b (c, β),
              (X.s3Del H b D' (X.tup Cz) (c, β)).w a) X.y₀).w (y u) := by
          have hqcondZ' := hqcondZ
          rw [← hβEq] at hqcondZ'
          unfold Ctx6.qRef
          dsimp only
          rw [if_pos hqcondZ']
          simpa [b, c, β, hβEq, hselCz]
        have hqC : (X.qRef H C v u).w (y u) =
            (normalize6 (fun a => ∑ D' ∈ X.descsWith H C b (c, β),
              (X.s3Del H b D' (X.tup C) (c, β)).w a) X.y₀).w (y u) := by
          have hqcondC' := hqcondC
          rw [← hβEq] at hqcondC'
          unfold Ctx6.qRef
          dsimp only
          rw [if_pos hqcondC']
        rw [hqZ, hnormEq, hqC]
      · have hmatch' : ¬ X.Matching (X.g.L.stateOf u.1) (X.evenType v) := by
          intro hother
          have hβEq' : β = X.evenType v := by simpa [β] using hβEq
          have hβ := hother
          rw [← hβEq'] at hβ
          exact hmatch (by simpa [b] using hβ)
        simp [Ctx6.qRef, hβEq, hmatch']
    have hF : X.Fz H C v c z y =
        ∏ u ∈ X.oddNbrs v, X.oddRow H Cz u.1 (y u) := by
      simp [Ctx6.Fz, Cz, c, β, hgate]
    let cost : OddRole6 n → ℝ := fun u =>
      if X.Matching (X.g.L.stateOf u.1) β then (25 / 100 : ℝ) * X.k
      else if X.stMode (X.g.L.stateOf u.1) = .low then (X.m : ℝ) ^ (15 / 100 : ℝ)
      else 500 * X.k
    have hhighCap : (n : ℝ) ^ ((5 / 100 : ℝ) * X.J) ≤ Real.exp (500 * X.k) := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast hdim)]
      apply Real.exp_le_exp.mpr
      have hscaled := mul_le_mul_of_nonneg_left hkceil (by norm_num : (0 : ℝ) ≤ 500)
      have hcoeff : 500 * κ₆ = (5 / 100 : ℝ) := by norm_num [κ₆]
      calc
        Real.log (n : ℝ) * ((5 / 100 : ℝ) * X.J) =
            500 * (κ₆ * (X.J : ℝ) * Real.log n) := by rw [← hcoeff]; ring
        _ ≤ 500 * X.k := hscaled
    have hrowExp : ∀ u : OddRole6 n, u ∈ X.oddNbrs v →
        X.oddRow H Cz u.1 (y u) ≤
          Real.exp (cost u) * (X.qRef H Cz v u).w (y u) := by
      intro u hu
      by_cases hmatch : X.Matching (X.g.L.stateOf u.1) β
      · simpa [cost, hmatch] using (hrowCompare u hu)
      · by_cases hlow : X.stMode (X.g.L.stateOf u.1) = .low
        · simpa [cost, hmatch, hlow] using (hrowCompare u hu)
        · have hcompare := hrowCompare u hu
          simp only [hmatch, hlow, if_false] at hcompare
          calc
            X.oddRow H Cz u.1 (y u) ≤
                (n : ℝ) ^ ((5 / 100 : ℝ) * X.J) * (X.qRef H Cz v u).w (y u) := hcompare
            _ ≤ Real.exp (500 * X.k) * (X.qRef H Cz v u).w (y u) :=
              mul_le_mul_of_nonneg_right hhighCap ((X.qRef H Cz v u).nonneg (y u))
            _ = Real.exp (cost u) * (X.qRef H Cz v u).w (y u) := by simp [cost, hmatch, hlow]
    have hrowNonneg : ∀ u : OddRole6 n, u ∈ X.oddNbrs v →
        0 ≤ X.oddRow H Cz u.1 (y u) := by
      intro u hu
      exact (hRows H Cz u.1 hH u.2 (hodd u hu)).1 (y u)
    have hqNonneg : ∀ u : OddRole6 n, u ∈ X.oddNbrs v →
        0 ≤ (X.qRef H C v u).w (y u) := by
      intro u hu
      exact (X.qRef H C v u).nonneg (y u)
    have hrowExpC : ∀ u : OddRole6 n, u ∈ X.oddNbrs v →
        X.oddRow H Cz u.1 (y u) ≤
          Real.exp (cost u) * (X.qRef H C v u).w (y u) := by
      intro u hu
      calc
        X.oddRow H Cz u.1 (y u) ≤
            Real.exp (cost u) * (X.qRef H Cz v u).w (y u) := hrowExp u hu
        _ = Real.exp (cost u) * (X.qRef H C v u).w (y u) := by rw [hqRefEq u hu]
    have hprod := Lane_q_s06_even.prod_le_exp_sum_mul_prod (X.oddNbrs v)
      (fun u => X.oddRow H Cz u.1 (y u))
      (fun u => (X.qRef H C v u).w (y u)) cost hrowNonneg hqNonneg hrowExpC
    have hNbrCard : (X.oddNbrs v).card ≤ n := by
      let adj : Finset (CubeVertex n) := Finset.univ.filter fun u => (cube n).Adj v u
      have hmap : ∀ u ∈ X.oddNbrs v, u.1 ∈ adj := by
        intro u hu
        have hu' : (cube n).Adj v u.1 := by
          simpa [Ctx6.oddNbrs] using hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu'⟩
      have hinj : (X.oddNbrs v : Set (OddRole6 n)).InjOn Subtype.val := by
        intro u hu w hw heq
        exact Subtype.ext heq
      calc
        (X.oddNbrs v).card ≤ adj.card := Finset.card_le_card_of_injOn Subtype.val hmap hinj
        _ ≤ n := by
          simpa [adj] using
            Lane_q_s06_even.adjacent_card_le_dimension_even v hdim
    let bad : Finset (OddRole6 n) := (X.oddNbrs v).filter
      (fun u => ¬ X.Matching (X.g.L.stateOf u.1) β)
    let fullBad : Finset (CubeVertex n) := Finset.univ.filter fun u =>
      (cube n).Adj v u ∧ ¬ X.Matching (X.g.L.stateOf u) (X.evenType v)
    let occupied : Finset (Fin n) :=
      (Finset.univ.biUnion X.g.L.coarseChunks) ∪ (Finset.univ.biUnion X.g.L.fineChunks)
    have hbadCard : bad.card ≤ occupied.card := by
      have hmap : ∀ u ∈ bad, u.1 ∈ fullBad := by
        intro u hu
        have hu' := Finset.mem_filter.mp hu
        have hadj : (cube n).Adj v u.1 := by
          simpa [Ctx6.oddNbrs] using hu'.1
        have hnot : ¬ X.Matching (X.g.L.stateOf u.1) (X.evenType v) := by
          intro hmatch
          have hβEq' : β = X.evenType v := by simpa [β] using hβEq
          have hmatchβ := hmatch
          rw [← hβEq'] at hmatchβ
          exact hu'.2 hmatchβ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hadj, hnot⟩⟩
      have hinj : (bad : Set (OddRole6 n)).InjOn Subtype.val := by
        intro u hu w hw heq
        exact Subtype.ext heq
      calc
        bad.card ≤ fullBad.card := Finset.card_le_card_of_injOn Subtype.val hmap hinj
        _ ≤ occupied.card := by
          simpa [fullBad, occupied] using
            Lane_q_s06_even.nonmatching_adjacent_card_le_occupied X v hdim
    have hbadReal : (bad.card : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
      have hcast : (bad.card : ℝ) ≤ (occupied.card : ℝ) := by exact_mod_cast hbadCard
      exact hcast.trans X.g.L.occupied_sublinear
    have hmcap : (X.m : ℝ) ^ (15 / 100 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        (X.m : ℝ) ^ (15 / 100 : ℝ) ≤ (n : ℝ) ^ (15 / 100 : ℝ) := by
          apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmle) (by norm_num)
        _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          · exact_mod_cast (show 1 ≤ n by omega)
          · norm_num
    have hsqrt : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) / 100000 := by
      rw [← Real.sqrt_eq_rpow]
      rw [Real.sqrt_le_left (by positivity)]
      have hnreal : (10 ^ 10 : ℝ) ≤ n := by exact_mod_cast hnlarge
      nlinarith
    have hcapTotal : (n : ℝ) ^ (1 / 2 : ℝ) *
        max ((X.m : ℝ) ^ (15 / 100 : ℝ)) (500 * X.k) ≤
          (9 / 100 : ℝ) * X.k * n := by
      have hlow : (n : ℝ) ^ (1 / 2 : ℝ) * (X.m : ℝ) ^ (15 / 100 : ℝ) ≤
          (9 / 100 : ℝ) * X.k * n := by
        calc
          (n : ℝ) ^ (1 / 2 : ℝ) * (X.m : ℝ) ^ (15 / 100 : ℝ) ≤
              (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) :=
                mul_le_mul_of_nonneg_left hmcap (by positivity)
          _ = n := by rw [← Real.rpow_add (by exact_mod_cast hdim)]; norm_num
          _ ≤ (9 / 100 : ℝ) * X.k * n := by
            have hkR : (12 : ℝ) ≤ X.k := by exact_mod_cast hklarge
            have hcoef : (1 : ℝ) ≤ (9 / 100 : ℝ) * X.k := by
              calc
                1 ≤ (9 / 100 : ℝ) * 12 := by norm_num
                _ ≤ (9 / 100 : ℝ) * X.k :=
                  mul_le_mul_of_nonneg_left hkR (by norm_num)
            calc
              (n : ℝ) = 1 * n := by ring
              _ ≤ ((9 / 100 : ℝ) * X.k) * n :=
                mul_le_mul_of_nonneg_right hcoef (by positivity)
              _ = (9 / 100 : ℝ) * X.k * n := by ring
      have hhigh : (n : ℝ) ^ (1 / 2 : ℝ) * (500 * X.k) ≤
          (9 / 100 : ℝ) * X.k * n := by
        calc
          (n : ℝ) ^ (1 / 2 : ℝ) * (500 * X.k) ≤
              ((n : ℝ) / 100000) * (500 * X.k) :=
                mul_le_mul_of_nonneg_right hsqrt (by positivity)
          _ ≤ (9 / 100 : ℝ) * X.k * n := by nlinarith [hdim]
      have hmulmax : (n : ℝ) ^ (1 / 2 : ℝ) *
          max ((X.m : ℝ) ^ (15 / 100 : ℝ)) (500 * X.k) =
            max ((n : ℝ) ^ (1 / 2 : ℝ) * (X.m : ℝ) ^ (15 / 100 : ℝ))
              ((n : ℝ) ^ (1 / 2 : ℝ) * (500 * X.k)) := by
        by_cases hxy : (X.m : ℝ) ^ (15 / 100 : ℝ) ≤ 500 * X.k
        · rw [max_eq_right hxy,
            max_eq_right (mul_le_mul_of_nonneg_left hxy (by positivity))]
        · have hyx : 500 * X.k ≤ (X.m : ℝ) ^ (15 / 100 : ℝ) := le_of_not_ge hxy
          rw [max_eq_left hyx,
            max_eq_left (mul_le_mul_of_nonneg_left hyx (by positivity))]
      rw [hmulmax]
      exact max_le_iff.mpr ⟨hlow, hhigh⟩
    have hcost : (∑ u ∈ X.oddNbrs v, cost u) ≤ (34 / 100 : ℝ) * X.k * n := by
      have hpoint : ∀ u ∈ X.oddNbrs v,
          cost u ≤ (25 / 100 : ℝ) * X.k +
            (if ¬ X.Matching (X.g.L.stateOf u.1) β then
              max ((X.m : ℝ) ^ (15 / 100 : ℝ)) (500 * X.k) else 0) := by
        intro u hu
        by_cases hmatch : X.Matching (X.g.L.stateOf u.1) β
        · simp [cost, hmatch]
        · by_cases hlow : X.stMode (X.g.L.stateOf u.1) = .low
          · have : (X.m : ℝ) ^ (15 / 100 : ℝ) ≤
                max ((X.m : ℝ) ^ (15 / 100 : ℝ)) (500 * X.k) := le_max_left _ _
            simp [cost, hmatch, hlow]
            linarith
          · have : 500 * X.k ≤ max ((X.m : ℝ) ^ (15 / 100 : ℝ)) (500 * X.k) :=
                le_max_right _ _
            simp [cost, hmatch, hlow]
            linarith
      calc
        (∑ u ∈ X.oddNbrs v, cost u) ≤
            ∑ u ∈ X.oddNbrs v,
              ((25 / 100 : ℝ) * X.k +
                (if ¬ X.Matching (X.g.L.stateOf u.1) β then
                  max ((X.m : ℝ) ^ (15 / 100 : ℝ)) (500 * X.k) else 0)) := by
              apply Finset.sum_le_sum
              intro u hu
              exact hpoint u hu
        _ = (X.oddNbrs v).card * ((25 / 100 : ℝ) * X.k) +
              bad.card * max ((X.m : ℝ) ^ (15 / 100 : ℝ)) (500 * X.k) := by
              have hsumBad :
                  (∑ u ∈ X.oddNbrs v,
                    if ¬ X.Matching (X.g.L.stateOf u.1) β then
                      max ((X.m : ℝ) ^ (15 / 100 : ℝ)) (500 * X.k) else 0) =
                    bad.card * max ((X.m : ℝ) ^ (15 / 100 : ℝ)) (500 * X.k) := by
                calc
                  _ = ∑ u ∈ (X.oddNbrs v).filter
                        (fun u => ¬ X.Matching (X.g.L.stateOf u.1) β),
                        max ((X.m : ℝ) ^ (15 / 100 : ℝ)) (500 * X.k) := by
                          rw [Finset.sum_filter]
                  _ = bad.card * max ((X.m : ℝ) ^ (15 / 100 : ℝ)) (500 * X.k) := by
                          simp [bad]
              rw [Finset.sum_add_distrib, hsumBad]
              simp [Finset.sum_const]
        _ ≤ (n : ℝ) * ((25 / 100 : ℝ) * X.k) +
              (n : ℝ) ^ (1 / 2 : ℝ) * max ((X.m : ℝ) ^ (15 / 100 : ℝ)) (500 * X.k) := by
              have hNbrReal : ((X.oddNbrs v).card : ℝ) ≤ n := by exact_mod_cast hNbrCard
              exact add_le_add
                (mul_le_mul_of_nonneg_right hNbrReal (by positivity))
                (mul_le_mul_of_nonneg_right hbadReal (by positivity))
        _ ≤ (34 / 100 : ℝ) * X.k * n := by
              calc
                (n : ℝ) * ((25 / 100 : ℝ) * X.k) +
                (n : ℝ) ^ (1 / 2 : ℝ) * max ((X.m : ℝ) ^ (15 / 100 : ℝ)) (500 * X.k) ≤
                  (n : ℝ) * ((25 / 100 : ℝ) * X.k) + (9 / 100 : ℝ) * X.k * n :=
                  add_le_add le_rfl hcapTotal
                _ = (34 / 100 : ℝ) * X.k * n := by ring
    change X.Fz H C v c z y ≤
      Real.exp ((34 / 100 : ℝ) * X.k * n) * X.Qref H C v y
    rw [hF, Ctx6.Qref]
    calc
      (∏ u ∈ X.oddNbrs v, X.oddRow H Cz u.1 (y u)) ≤
          Real.exp (∑ u ∈ X.oddNbrs v, cost u) *
            ∏ u ∈ X.oddNbrs v, (X.qRef H C v u).w (y u) := hprod
      _ ≤ Real.exp ((34 / 100 : ℝ) * X.k * n) *
            ∏ u ∈ X.oddNbrs v, (X.qRef H C v u).w (y u) := by
          apply mul_le_mul_of_nonneg_right _
            (Finset.prod_nonneg fun u hu => (X.qRef H C v u).nonneg (y u))
          exact Real.exp_le_exp.mpr hcost

  · have hFzero : X.Fz H C v c z y = 0 := by
      change (if X.EvenGate H Cz v c then 1 else 0) *
        (∏ u ∈ X.oddNbrs v, X.oddRow H Cz u.1 (y u)) = 0
      rw [if_neg hgate]
      simp
    rw [hFzero]
    apply mul_nonneg (Real.exp_nonneg _)
    exact Finset.prod_nonneg fun u hu => (X.qRef H C v u).nonneg (y u)

set_option maxHeartbeats 50000000

/-- L6.1m (tests, 06:813–824): keep the successful prehistory while comparing the queried odd labels with the
product law (`JfOK`), drop nonlocal success, keep `E`; Lemma 3.7 bounds each `(v, c)` by `(1+o(1))e^{−.02kn}`;
the union over `exp(O(n))` pairs. -/
theorem L6_1m_test (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.HistSupport → X.EvenDom → X.EvenGateDet → X.EvenTest := by
  have hp₀ : 0 < p₀ := hadm.2.2.1
  obtain ⟨nGrowth, hGrowth⟩ := Lane_q_s06_ev_a.parameter_growth p₀ hp₀
  obtain ⟨nScale, hScale⟩ := Lane_q_s06_ev_a.topScale_fourth_eventually p₀ hp₀
  refine ⟨max nGrowth nScale, 1, ?_⟩
  intro n N E G M X hL hSupport hDom hGateDet
  classical
  have hGrowthN := hGrowth n (le_trans (le_max_left _ _) hL.1)
  rcases hGrowthN with ⟨hJgrowth, hTgrowth, hlogTgrowth, hmGrowth, hkGrowth, hnGrowth⟩
  have hScaleN := hScale n (le_trans (le_max_right _ _) hL.1)
  have hJlarge : 2000000 ≤ X.J := by
    simpa [Ctx6.J, Ctx6.m, X.g.m_eq, J₆, m₆] using hJgrowth
  have hnlarge : 10 ^ 10 ≤ n := hnGrowth
  have hkceil : κ₆ * (X.J : ℝ) * Real.log n ≤ (X.k : ℝ) := by
    dsimp [Ctx6.k, k₆]
    exact Nat.le_ceil _
  have hlogn : 20 ≤ Real.log n := by
    have hlogTwo := Lane_q_s06_ev_a.log_two_lower6
    have hlogEight : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      calc
        Real.log 8 = Real.log ((2 : ℝ) ^ 3) := by congr 1 <;> norm_num
        _ = 3 * Real.log 2 := Real.log_pow 2 3
    have hlogTen : 2 ≤ Real.log (10 : ℝ) := by
      have hmon := Real.log_le_log (by norm_num : (0 : ℝ) < 8)
        (by norm_num : (8 : ℝ) ≤ 10)
      rw [hlogEight] at hmon
      nlinarith
    have hnR : (10 ^ 10 : ℝ) ≤ n := by exact_mod_cast hnlarge
    have hlogMon := Real.log_le_log (by norm_num : (0 : ℝ) < 10 ^ 10) hnR
    rw [Real.log_pow] at hlogMon
    calc
      20 ≤ 10 * Real.log (10 : ℝ) := by nlinarith
      _ ≤ Real.log n := hlogMon
  have hklog : (200 : ℝ) * Real.log n ≤ X.k := by
    have hJreal : (2000000 : ℝ) ≤ X.J := by exact_mod_cast hJlarge
    have hJmul : (2000000 : ℝ) * Real.log n ≤ X.J * Real.log n :=
      mul_le_mul_of_nonneg_right hJreal (by linarith [hlogn])
    have hκ : κ₆ * 2000000 = 200 := by norm_num [κ₆]
    nlinarith [hkceil, hJmul, hκ]
  have hNlower : (2 : ℝ) ^ n ≤ (N : ℝ) := by simpa using hL.2.1
  have hNposR : 0 < (N : ℝ) := lt_of_lt_of_le (by positivity) hNlower
  have hNpos : 0 < N := by exact_mod_cast hNposR
  have hdim : 0 < n := by omega
  have hPow := Lane_q_s06_ev_a.large_power_bounds6 hnlarge
  have hLocCard : Fintype.card X.Loc ≤ 2 ^ (7 * n) := by
    have hd : X.code.d ≤ 2 * n := by
      have hdR : (X.code.d : ℝ) ≤ 2 * n := by simpa [Cd₆] using X.code.d_upper
      exact_mod_cast hdR
    have hnatAll : ∀ m : ℕ, m ≤ 2 ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          by_cases hm : m = 0
          · simp [hm]
          · have hmpos : 1 ≤ m := by omega
            have hstep : m + 1 ≤ 2 * m := by omega
            have hp' : 2 * m ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
            calc
              m + 1 ≤ 2 * m := hstep
              _ ≤ 2 * 2 ^ m := hp'
              _ = 2 ^ (m + 1) := by rw [pow_succ]; omega
    have hnat : n ≤ 2 ^ n := hnatAll n
    have hpow4 : n ^ 4 ≤ 2 ^ (4 * n) := by
      calc
        n ^ 4 ≤ (2 ^ n) ^ 4 := Nat.pow_le_pow_left hnat 4
        _ = 2 ^ (4 * n) := by rw [← pow_mul]; congr 1; omega
    have hpow41 : n ^ 4 + 1 ≤ 2 ^ (5 * n) := by
      have hn1 : 1 ≤ n := by omega
      have hdouble : 2 ^ (4 * n) + 2 ^ (4 * n) = 2 ^ (4 * n + 1) := by
        calc
          _ = 2 * 2 ^ (4 * n) := by ring
          _ = 2 ^ (4 * n + 1) := by rw [pow_succ]; ring
      have hfour : 4 * n + 1 ≤ 5 * n := by omega
      have hpowpos : 1 ≤ 2 ^ (4 * n) := Nat.one_le_pow' (4 * n) 1
      calc
        n ^ 4 + 1 ≤ 2 ^ (4 * n) + 2 ^ (4 * n) := Nat.add_le_add hpow4 hpowpos
        _ = 2 ^ (4 * n + 1) := hdouble
        _ ≤ 2 ^ (5 * n) := Nat.pow_le_pow_right (by omega) hfour
    have hHscale : X.hp.H ≤ n ^ 4 := by
      simpa [Ctx6.hp, σ₆, ζ₆, α₆] using hScaleN
    have hH : X.hp.H + 1 ≤ n ^ 4 + 1 := Nat.succ_le_succ hHscale
    have hcard : Fintype.card X.Loc = 2 ^ X.code.d * (X.hp.H + 1) := by
      change Fintype.card (CubeVertex X.code.d × Fin (X.hp.H + 1)) = _
      simp
    calc
      Fintype.card X.Loc = 2 ^ X.code.d * (X.hp.H + 1) := hcard
      _ ≤ 2 ^ (2 * n) * (n ^ 4 + 1) := by
        exact Nat.mul_le_mul
          (Nat.pow_le_pow_right (by omega) hd) hH
      _ ≤ 2 ^ (2 * n) * 2 ^ (5 * n) := Nat.mul_le_mul_left _ hpow41
      _ = 2 ^ (7 * n) := by rw [← pow_add]; congr 1; omega
  have hCubeCard : Fintype.card (CubeVertex n) = 2 ^ n := by simp
  let ε : ℝ := Real.exp (-(2 / 100 : ℝ) * X.k * n)
  have hεpos : 0 < ε := Real.exp_pos _
  have hεsmall : ε ≤ Real.exp (-(4 : ℝ) * Real.log n * n) := by
    rw [show ε = Real.exp (-(2 / 100 : ℝ) * X.k * n) from rfl]
    apply Real.exp_le_exp.mpr
    have hklog' := mul_le_mul_of_nonneg_right hklog (by positivity : (0 : ℝ) ≤ n)
    nlinarith [hklog']
  have hOddRowNonneg (H : X.Hist) (C : X.Centre) (u : CubeVertex n) (a : Fin N) :
      0 ≤ X.oddRow H C u a := by
    change 0 ≤ X.oddRowAt H C X.Rlong (X.g.L.stateOf u) a
    unfold Ctx6.oddRowAt
    by_cases hvalid : X.OddValid H C X.Rlong (X.g.L.stateOf u)
    · rw [if_pos hvalid]
      cases hm : X.stMode (X.g.L.stateOf u) with
      | low =>
          simp only [hm]
          exact (X.lowRow H (X.pos C) (X.g.L.stateOf u)
            (X.actDesc H C X.Rlong (X.g.L.stateOf u)) (X.tup C)).nonneg a
      | high =>
          simp only [hm]
          exact (X.s3Post H (X.g.L.stateOf u)
            (X.actDesc H C X.Rlong (X.g.L.stateOf u)) (X.tup C)).nonneg a
    · simp [hvalid]
  have hStarCard (v : CubeVertex n) : (X.oddNbrs v).card ≤ n := by
    let adj : Finset (CubeVertex n) := Finset.univ.filter fun u => (cube n).Adj v u
    have hmap : ∀ u ∈ X.oddNbrs v, u.1 ∈ adj := by
      intro u hu
      have hu' : (cube n).Adj v u.1 := by
        simpa [Ctx6.oddNbrs] using hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu'⟩
    have hinj : (X.oddNbrs v : Set (OddRole6 n)).InjOn Subtype.val := by
      intro u hu w hw heq
      exact Subtype.ext heq
    calc
      (X.oddNbrs v).card ≤ adj.card := Finset.card_le_card_of_injOn Subtype.val hmap hinj
      _ ≤ n := by
        simpa [adj] using Lane_q_s06_even.adjacent_card_le_dimension_even v hdim
  have hNreal : (2 : ℝ) ^ n ≤ (N : ℝ) := hNlower
  have hStarCap (v : CubeVertex n) :
      ((X.oddNbrs v).card : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) := by
    have hcast : ((X.oddNbrs v).card : ℝ) ≤ n := by exact_mod_cast hStarCard v
    have hpowEq : (2 : ℝ) ^ ((n : ℝ) / 40) =
        ((2 : ℝ) ^ n) ^ (1 / 40 : ℝ) := by
      rw [show (n : ℝ) / 40 = (n : ℝ) * (1 / 40 : ℝ) by ring,
        Real.rpow_natCast_mul (by norm_num)]
    calc
      ((X.oddNbrs v).card : ℝ) ≤ n := hcast
      _ ≤ (2 : ℝ) ^ ((n : ℝ) / 40) := hPow.1
      _ = ((2 : ℝ) ^ n) ^ (1 / 40 : ℝ) := hpowEq
      _ ≤ (N : ℝ) ^ (1 / 40 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hNreal (by norm_num)
  have hApprox : ∀ v : CubeVertex n,
      Real.exp ((N : ℝ) ^ (-(1 / 25 : ℝ)) * (X.oddNbrs v).card) ≤ 2 := by
    intro v
    have hlogN : (n : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
      have h := Real.log_le_log (by positivity) hNreal
      simpa [Real.log_pow] using h
    have hδ : (N : ℝ) ^ (-(1 / 25 : ℝ)) ≤
        (2 : ℝ) ^ (-(n : ℝ) / 25) := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast hNpos),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonpos_right hlogN
        (by norm_num : (-(1 / 25 : ℝ)) ≤ 0)
      nlinarith [hmul]
    have hpowPos : 0 < (2 : ℝ) ^ ((n : ℝ) / 25) := Real.rpow_pos_of_pos (by norm_num) _
    have hsmall : (n : ℝ) * ((2 : ℝ) ^ ((n : ℝ) / 25))⁻¹ ≤ 1 / 2 := by
      have hmul := mul_le_mul_of_nonneg_right hPow.2
        (inv_nonneg.mpr hpowPos.le)
      have hcancel : (2 : ℝ) ^ ((n : ℝ) / 25) *
          ((2 : ℝ) ^ ((n : ℝ) / 25))⁻¹ = 1 := mul_inv_cancel₀ hpowPos.ne'
      rw [hcancel] at hmul
      nlinarith [hmul]
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      linarith [Lane_q_s06_ev_a.log_two_lower6]
    have hdeltaS : (N : ℝ) ^ (-(1 / 25 : ℝ)) * (X.oddNbrs v).card ≤ 1 / 2 := by
      calc
        (N : ℝ) ^ (-(1 / 25 : ℝ)) * (X.oddNbrs v).card ≤
            (2 : ℝ) ^ (-(n : ℝ) / 25) * n :=
              mul_le_mul hδ (by exact_mod_cast hStarCard v)
                (by positivity) (by positivity)
        _ = (n : ℝ) * ((2 : ℝ) ^ ((n : ℝ) / 25))⁻¹ := by
              have hneg : (2 : ℝ) ^ (-(n : ℝ) / 25) =
                  ((2 : ℝ) ^ ((n : ℝ) / 25))⁻¹ := by
                have h := Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)
                  ((n : ℝ) / 25)
                have heq : -(n : ℝ) / 25 = -((n : ℝ) / 25) := by ring
                rw [heq]
                exact h
              rw [hneg]
              ring
        _ ≤ 1 / 2 := hsmall
    calc
      Real.exp ((N : ℝ) ^ (-(1 / 25 : ℝ)) * (X.oddNbrs v).card) ≤
          Real.exp (1 / 2) := Real.exp_le_exp.mpr hdeltaS
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hlog2
      _ = 2 := Real.exp_log (by norm_num)
  have hApproxStar (v : CubeVertex n) :
      Real.exp ((N : ℝ) ^ (-(0.04 : ℝ)) * (X.oddNbrs v).card) ≤ 2 := by
    convert hApprox v using 1 <;> norm_num
  let starExtend := fun (v : CubeVertex n)
      (a : (∀ u : {u : OddRole6 n // u ∈ X.oddNbrs v}, Fin N)) =>
    fun u : OddRole6 n => if h : u ∈ X.oddNbrs v then a ⟨u, h⟩ else X.y₀
  let starProject := fun (v : CubeVertex n) (y : OddRole6 n → Fin N) =>
    fun u : {u : OddRole6 n // u ∈ X.oddNbrs v} => y u.1
  let starFail := fun (H : X.Hist) (C : X.Centre) (v : CubeVertex n)
      (y : OddRole6 n → Fin N) =>
    ¬ (0 < X.mc H C v y ∧ ε * X.Qref H C v y ≤ X.mc H C v y)
  let starRowMass := fun (H : X.Hist) (C : X.Centre) (v : CubeVertex n)
      (a : ∀ u : {u : OddRole6 n // u ∈ X.oddNbrs v}, Fin N) =>
    ∏ u ∈ X.oddNbrs v, X.oddRow H C u.1 (starExtend v a u)
  let starBadMass := fun (H : X.Hist) (C : X.Centre) (v : CubeVertex n) =>
    ∑ a : (∀ u : {u : OddRole6 n // u ∈ X.oddNbrs v}, Fin N),
      if starFail H C v (starExtend v a) then starRowMass H C v a else 0
  have hStarBadNonneg (H : X.Hist) (C : X.Centre) (v : CubeVertex n) :
      0 ≤ starBadMass H C v := by
    unfold starBadMass
    apply Finset.sum_nonneg
    intro a ha
    split_ifs
    · apply Finset.prod_nonneg
      intro u hu
      exact hOddRowNonneg H C u.1 (starExtend v a u)
    · exact le_rfl
  have hPerStar (Jf : X.Hist → X.Centre → FinProb (OddRole6 n → Fin N))
      (hJf : X.JfOK Jf) (H : X.Hist) (hH : X.histLaw.w H ≠ 0)
      (C : X.Centre) (hGood : X.OddGood H C) (v : CubeVertex n) :
      (Jf H C).pr (fun y => starFail H C v y) ≤ 2 * starBadMass H C v := by
    let S := X.oddNbrs v
    have hSize : (S.card : ℝ) ≤ (N : ℝ) ^ (0.025 : ℝ) := by
      simpa [S, show (0.025 : ℝ) = 1 / 40 by norm_num] using hStarCap v
    have hExtProj (y : OddRole6 n → Fin N) (u : OddRole6 n) (hu : u ∈ S) :
        starExtend v (starProject v y) u = y u := by
      simp [starExtend, starProject, S, hu]
    have hMcExt (y : OddRole6 n → Fin N) :
        X.mc H C v (starExtend v (starProject v y)) = X.mc H C v y := by
      unfold Ctx6.mc
      apply Finset.sum_congr rfl
      intro z hz
      congr 1
      unfold Ctx6.Fz
      congr 1
      apply Finset.prod_congr rfl
      intro u hu
      rw [hExtProj y u hu]
    have hQExt (y : OddRole6 n → Fin N) :
        X.Qref H C v (starExtend v (starProject v y)) = X.Qref H C v y := by
      unfold Ctx6.Qref
      apply Finset.prod_congr rfl
      intro u hu
      rw [hExtProj y u hu]
    have hFailExt (y : OddRole6 n → Fin N) :
        starFail H C v (starExtend v (starProject v y)) = starFail H C v y := by
      unfold starFail
      rw [hMcExt y, hQExt y]
    have hAtomBound : ∀ a : ∀ u : {u : OddRole6 n // u ∈ S}, Fin N,
        (Jf H C).pr (fun y => starProject v y = a) ≤
          Real.exp ((N : ℝ) ^ (-(0.04 : ℝ)) * S.card) * starRowMass H C v a := by
      intro a
      have hAtomEq :
          (Jf H C).pr (fun y => starProject v y = a) =
            (Jf H C).pr (fun y => ∀ u ∈ S, y u = starExtend v a u) := by
        congr 1
        funext y
        apply propext
        constructor
        · intro hy u hu
          have h := congrFun hy ⟨u, hu⟩
          simpa [starProject, starExtend, S, hu] using h
        · intro hy
          funext u
          have h := hy u.1 u.2
          simpa [starProject, starExtend, S, u.2] using h
      rw [hAtomEq]
      exact (hJf H C hH hGood).2.2 S (starExtend v a) hSize
    let projectedFail : (∀ u : {u : OddRole6 n // u ∈ S}, Fin N) → Prop :=
      fun a => starFail H C v (starExtend v a)
    letI : DecidablePred projectedFail := fun a => Classical.propDecidable (projectedFail a)
    let projectedMass : (∀ u : {u : OddRole6 n // u ∈ S}, Fin N) → ℝ :=
      fun a => Real.exp ((N : ℝ) ^ (-(0.04 : ℝ)) * S.card) * starRowMass H C v a
    have hProjBound :
        (Jf H C).pr (fun y => projectedFail (starProject v y)) ≤
          ∑ a ∈ Finset.univ.filter projectedFail, projectedMass a :=
      Lane_q_s06_even.pr_event_le_sum_atoms
        (Jf H C) (starProject v) projectedFail projectedMass hAtomBound
    have hEventEq :
        (Jf H C).pr (fun y => starFail H C v y) =
          (Jf H C).pr (fun y => starFail H C v (starExtend v (starProject v y))) := by
      congr 1
      funext y
      exact (hFailExt y).symm
    rw [hEventEq]
    calc
      (Jf H C).pr (fun y => starFail H C v (starExtend v (starProject v y))) ≤
          ∑ a ∈ Finset.univ.filter projectedFail, projectedMass a := by
              simpa [projectedFail] using hProjBound
      _ = Real.exp ((N : ℝ) ^ (-(0.04 : ℝ)) * S.card) * starBadMass H C v := by
        dsimp [projectedFail, projectedMass]
        unfold starBadMass
        rw [Finset.sum_filter]
        have hpoint (a : ↥S → Fin N) :
            (if starFail H C v (starExtend v a) then
              Real.exp ((N : ℝ) ^ (-(0.04 : ℝ)) * S.card) *
                starRowMass H C v a else 0) =
              Real.exp ((N : ℝ) ^ (-(0.04 : ℝ)) * S.card) *
                (if starFail H C v (starExtend v a) then
                  starRowMass H C v a else 0) := by
          by_cases hb : starFail H C v (starExtend v a) <;> simp [hb]
        simp_rw [hpoint]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hb : starFail H C v (starExtend v a) <;> simp [hb]
      _ ≤ 2 * starBadMass H C v :=
        mul_le_mul_of_nonneg_right (by simpa [S] using hApproxStar v)
          (hStarBadNonneg H C v)
  have hCenterBad (H : X.Hist) (hH : X.histLaw.w H ≠ 0)
      (v : CubeVertex n) (hv : IsEvenRole v) :
      (X.centreLaw H).expect (fun C =>
        if X.OddGood H C then starBadMass H C v else 0) ≤
          (Fintype.card X.Loc : ℝ) * ε := by
    let β := X.evenTy v
    have hpoint (C : X.Centre) :
        (if X.OddGood H C then starBadMass H C v else 0) =
          ∑ c : X.Loc,
            if X.OddGood H C ∧ X.selC H C v = c then starBadMass H C v else 0 := by
      by_cases hGoodC : X.OddGood H C
      · simp [hGoodC, Finset.sum_ite_eq]
      · simp [hGoodC]
    have hByC (c : X.Loc) :
        (X.centreLaw H).expect (fun C =>
          if X.OddGood H C ∧ X.selC H C v = c then starBadMass H C v else 0) ≤ ε := by
      let e : X.Loc × X.Ty := (c, β)
      let f : X.Centre → ℝ := fun C =>
        if X.OddGood H C ∧ X.selC H C v = c then starBadMass H C v else 0
      have hsplit := Lane_q_s06_ev_a.centreLaw_expect_split6 X H e f
      rw [hsplit]
      have hLocal (r : Lane_q_s06_ev_a.CentreRest6 X e) :
          ∑ z : X.Tuple, (X.tupleLaw H β).w z *
            f (Lane_q_s06_ev_a.centreFromParts6 X e z r) ≤ ε := by
        let z₀ : X.Tuple := (X.i₀, fun _ : Fin X.k => X.y₀)
        let C₀ : X.Centre := Lane_q_s06_ev_a.centreFromParts6 X e z₀ r
        let Cz : X.Tuple → X.Centre := fun z =>
          Lane_q_s06_ev_a.centreFromParts6 X e z r
        let S := X.oddNbrs v
        let qAt : (∀ u : {u : OddRole6 n // u ∈ S}, Law N) := fun u =>
          let b := X.g.L.stateOf u.1.1
          if X.Matching b β ∧ (X.descsWith H C₀ b e).Nonempty then
            normalize6 (fun a => ∑ D' ∈ X.descsWith H C₀ b e,
              (X.s3Del H b D' (X.tup C₀) e).w a) X.y₀
          else X.unifLaw
        let Qlaw : FinProb (∀ u : {u : OddRole6 n // u ∈ S}, Fin N) := FinProb.pi qAt
        let π : FinProb X.Tuple := X.tupleLaw H β
        let F : X.Tuple → (∀ u : {u : OddRole6 n // u ∈ S}, Fin N) → ℝ := fun z a =>
          X.Fz H C₀ v c z (starExtend v a)
        let m : (∀ u : {u : OddRole6 n // u ∈ S}, Fin N) → ℝ := fun a =>
          ∑ z : X.Tuple, π.w z * F z a
        let bad₀ : (∀ u : {u : OddRole6 n // u ∈ S}, Fin N) → Prop := fun a =>
          ¬ (0 < m a ∧ ε * Qlaw.w a ≤ m a)
        have hF0 (z : X.Tuple) (a : ∀ u : {u : OddRole6 n // u ∈ S}, Fin N) :
            0 ≤ F z a := by
          unfold F Ctx6.Fz
          apply mul_nonneg
          · split_ifs <;> norm_num
          · apply Finset.prod_nonneg
            intro u hu
            exact hOddRowNonneg H (X.withTuple C₀ (c, β) z) u.1
              (starExtend v a u)
        have hmNonneg (a : ∀ u : {u : OddRole6 n // u ∈ S}, Fin N) : 0 ≤ m a := by
          unfold m
          apply Finset.sum_nonneg
          intro z hz
          exact mul_nonneg (π.nonneg z) (hF0 z a)
        have hpost := HypercubeRamsey.gated_posterior π F hF0 Qlaw ε 0 hεpos
        have hbadIff (a : ∀ u : {u : OddRole6 n // u ∈ S}, Fin N) :
            bad₀ a ↔ m a < ε * Qlaw.w a ∨ m a = 0 := by
          unfold bad₀
          by_cases hz : m a = 0
          · simp [hz]
          · have hmpos : 0 < m a := lt_of_le_of_ne (hmNonneg a) (Ne.symm hz)
            constructor
            · intro hbad
              left
              apply lt_of_not_ge
              intro hge
              exact hbad ⟨hmpos, hge⟩
            · rintro (hlt | hzero) ⟨hpos, hge⟩
              · exact (not_lt_of_ge hge) hlt
              · exact (hz hzero).elim
        have hpostBad :
            (∑ a, if bad₀ a then m a else 0) ≤ ε := by
          simpa [m, bad₀, hbadIff] using hpost.1
        have hTupUpdate (z : X.Tuple) :
            X.tup (Cz z) = Function.update (X.tup C₀) e z := by
          funext q
          by_cases hq : q = e
          · subst q
            simp [Cz, C₀, Ctx6.tup, Lane_q_s06_ev_a.centreFromParts6,
              Lane_q_s06_ev_a.dataFromParts6]
          · simp [Cz, C₀, Ctx6.tup, Lane_q_s06_ev_a.centreFromParts6,
              Lane_q_s06_ev_a.dataFromParts6, hq]
        have hPos (z : X.Tuple) : X.pos (Cz z) = X.pos C₀ := rfl
        have hAct (z : X.Tuple) : X.act (Cz z) = X.act C₀ := rfl
        have hTies (z : X.Tuple) : X.ties (Cz z) = X.ties C₀ := rfl
        have hWith (z z' : X.Tuple) :
            X.withTuple (Cz z) e z' = X.withTuple C₀ e z' := by
          change (((X.pos (Cz z), Function.update (X.tup (Cz z)) e z'),
              X.act (Cz z)), X.ties (Cz z)) =
            (((X.pos C₀, Function.update (X.tup C₀) e z'), X.act C₀), X.ties C₀)
          rw [hPos z, hAct z, hTies z, hTupUpdate z]
          simp
        have hTupAt (z : X.Tuple) : X.tup (Cz z) e = z := by
          simp [Cz, Ctx6.tup, Lane_q_s06_ev_a.centreFromParts6,
            Lane_q_s06_ev_a.dataFromParts6]
        have hWithSelf (z : X.Tuple) : X.withTuple (Cz z) e z = Cz z := by
          change (((X.pos (Cz z), Function.update (X.tup (Cz z)) e z),
              X.act (Cz z)), X.ties (Cz z)) = Cz z
          have hupdate : Function.update (X.tup (Cz z)) e z = X.tup (Cz z) := by
            funext q
            by_cases hq : q = e
            · subst q
              simp [hTupAt z]
            · simp [Function.update_of_ne, hq]
          rw [hupdate]
          rfl
        have hBaseCz (z : X.Tuple) : X.withTuple C₀ e z = Cz z := by
          calc
            X.withTuple C₀ e z = X.withTuple (Cz z) e z := (hWith z z).symm
            _ = Cz z := hWithSelf z
        have hFamEq (z : X.Tuple) (u : OddRole6 n) :
            X.descsWith H (Cz z) (X.g.L.stateOf u.1) e =
              X.descsWith H C₀ (X.g.L.stateOf u.1) e := by
          simp [Ctx6.descsWith, hPos z]
        have hDelEq (z : X.Tuple) (b : X.State)
            (D' : Finset (X.Loc × X.Ty)) :
            X.s3Del H b D' (X.tup (Cz z)) e = X.s3Del H b D' (X.tup C₀) e := by
          rw [hTupUpdate z]
          exact Lane_q_s06_ev_a.s3Del_update_irrelevant X H b D' (X.tup C₀) e z
        have hqAtEq (z : X.Tuple) (hsel : X.selC H (Cz z) v = c)
            (u : OddRole6 n) (hu : u ∈ S) :
            X.qRef H (Cz z) v u = qAt ⟨u, hu⟩ := by
          let b : X.State := X.g.L.stateOf u.1
          have hFamEqPair : X.descsWith H (Cz z) b (c, X.evenTy v) =
              X.descsWith H C₀ b (c, X.evenTy v) := by
            simpa [e, β, b] using hFamEq z u
          have hDelEqPair (D' : Finset (X.Loc × X.Ty)) :
              X.s3Del H b D' (X.tup (Cz z)) (c, X.evenTy v) =
                X.s3Del H b D' (X.tup C₀) (c, X.evenTy v) := by
            simpa [e, β, b] using hDelEq z b D'
          unfold Ctx6.qRef
          dsimp only
          rw [hsel]
          unfold qAt
          dsimp only
          change (if X.Matching (X.g.L.stateOf u.1) (X.evenTy v) ∧
                (X.descsWith H (Cz z) (X.g.L.stateOf u.1)
                  (c, X.evenTy v)).Nonempty then
              normalize6 (fun a => ∑ D' ∈ X.descsWith H (Cz z)
                (X.g.L.stateOf u.1) (c, X.evenTy v),
                  (X.s3Del H (X.g.L.stateOf u.1) D' (X.tup (Cz z))
                    (c, X.evenTy v)).w a) X.y₀
            else X.unifLaw) =
            (if X.Matching (X.g.L.stateOf u.1) (X.evenTy v) ∧
                (X.descsWith H C₀ (X.g.L.stateOf u.1)
                  (c, X.evenTy v)).Nonempty then
              normalize6 (fun a => ∑ D' ∈ X.descsWith H C₀
                (X.g.L.stateOf u.1) (c, X.evenTy v),
                  (X.s3Del H (X.g.L.stateOf u.1) D' (X.tup C₀)
                    (c, X.evenTy v)).w a) X.y₀
            else X.unifLaw)
          by_cases hmatch : X.Matching (X.g.L.stateOf u.1) (X.evenTy v)
          · by_cases hne : (X.descsWith H C₀ (X.g.L.stateOf u.1)
                (c, X.evenTy v)).Nonempty
            · have hneZ : (X.descsWith H (Cz z) (X.g.L.stateOf u.1)
                  (c, X.evenTy v)).Nonempty := by
                rw [hFamEqPair]
                exact hne
              rw [if_pos ⟨hmatch, hneZ⟩, if_pos ⟨hmatch, hne⟩]
              rw [hFamEqPair]
              apply congrArg (fun f => normalize6 f X.y₀)
              funext a
              apply Finset.sum_congr rfl
              intro D' hD
              exact congrArg (fun law => law.w a) (hDelEqPair D')
            · have hneZ : ¬ (X.descsWith H (Cz z) (X.g.L.stateOf u.1)
                  (c, X.evenTy v)).Nonempty := by
                intro hz
                apply hne
                rw [← hFamEqPair]
                exact hz
              rw [if_neg (fun h => hneZ h.2), if_neg (fun h => hne h.2)]
          · have hnotZ : ¬ (X.Matching (X.g.L.stateOf u.1) (X.evenTy v) ∧
                (X.descsWith H (Cz z) (X.g.L.stateOf u.1)
                  (c, X.evenTy v)).Nonempty) := fun h => hmatch h.1
            have hnot0 : ¬ (X.Matching (X.g.L.stateOf u.1) (X.evenTy v) ∧
                (X.descsWith H C₀ (X.g.L.stateOf u.1)
                  (c, X.evenTy v)).Nonempty) := fun h => hmatch h.1
            rw [if_neg hnotZ, if_neg hnot0]
        have hQeq (z : X.Tuple) (hsel : X.selC H (Cz z) v = c)
            (a : ∀ u : {u : OddRole6 n // u ∈ S}, Fin N) :
            Qlaw.w a = X.Qref H (Cz z) v (starExtend v a) := by
          let g : OddRole6 n → ℝ := fun u =>
            if hu : u ∈ S then (qAt ⟨u, hu⟩).w (a ⟨u, hu⟩) else 1
          have hattach : Qlaw.w a = ∏ u ∈ S, g u := by
            change (∏ u : {u : OddRole6 n // u ∈ S}, (qAt u).w (a u)) = _
            rw [Finset.univ_eq_attach]
            simpa [g] using Finset.prod_attach S g
          calc
            Qlaw.w a = ∏ u ∈ S, g u := hattach
            _ = ∏ u ∈ S,
                (X.qRef H (Cz z) v u).w (starExtend v a u) := by
                  apply Finset.prod_congr rfl
                  intro u hu
                  have hq := hqAtEq z hsel u hu
                  have hq' := congrArg (fun law => law.w (starExtend v a u)) hq.symm
                  simpa [g, hu, starExtend, S] using hq'
            _ = X.Qref H (Cz z) v (starExtend v a) := by
                  rfl
        have hMcEq (z : X.Tuple) (hsel : X.selC H (Cz z) v = c)
            (a : ∀ u : {u : OddRole6 n // u ∈ S}, Fin N) :
            X.mc H (Cz z) v (starExtend v a) = m a := by
          unfold Ctx6.mc m F
          rw [hsel]
          apply Finset.sum_congr rfl
          intro z' hz'
          have hcent : X.withTuple (Cz z) (c, X.evenTy v) z' =
              X.withTuple C₀ e z' := by simpa [e, β] using hWith z z'
          have hFz : X.Fz H (Cz z) v c z' (starExtend v a) =
              X.Fz H C₀ v c z' (starExtend v a) := by
            unfold Ctx6.Fz
            rw [hcent]
          exact congrArg (fun w => π.w z' * w) hFz
        have hGateAt (z : X.Tuple) (hGood : X.OddGood H (Cz z))
            (hsel : X.selC H (Cz z) v = c) : X.EvenGate H (Cz z) v c := by
          have h := hGateDet H (Cz z) v hH hGood hv
          simpa [hsel] using h
        have hFactual (z : X.Tuple) (a : ∀ u : {u : OddRole6 n // u ∈ S}, Fin N)
            (hGood : X.OddGood H (Cz z)) (hsel : X.selC H (Cz z) v = c) :
            F z a = starRowMass H (Cz z) v a := by
          unfold F starRowMass Ctx6.Fz
          rw [hBaseCz z]
          rw [if_pos (hGateAt z hGood hsel)]
          simp
        have hbadEq (z : X.Tuple) (a : ∀ u : {u : OddRole6 n // u ∈ S}, Fin N)
            (hsel : X.selC H (Cz z) v = c) :
            starFail H (Cz z) v (starExtend v a) = bad₀ a := by
          unfold starFail bad₀
          rw [hMcEq z hsel a, ← hQeq z hsel a]
        have hRaw (z : X.Tuple) :
            f (Cz z) ≤ ∑ a, if bad₀ a then F z a else 0 := by
          have hRHSnonneg : 0 ≤ ∑ a,
              if bad₀ a then F z a else 0 := by
            apply Finset.sum_nonneg
            intro a ha
            split_ifs
            · exact hF0 z a
            · exact le_rfl
          by_cases hGood : X.OddGood H (Cz z)
          · by_cases hsel : X.selC H (Cz z) v = c
            · have hEq : starBadMass H (Cz z) v =
                  ∑ a, if bad₀ a then F z a else 0 := by
                unfold starBadMass
                apply Finset.sum_congr rfl
                intro a ha
                by_cases hbad : starFail H (Cz z) v (starExtend v a)
                · have hbad' : bad₀ a := by
                    simpa [hbadEq z a hsel] using hbad
                  simp [hbad, hbad', hFactual z a hGood hsel]
                · have hbad' : ¬ bad₀ a := by
                    simpa [hbadEq z a hsel] using hbad
                  simp [hbad, hbad']
              simpa [f, hGood, hsel] using hEq.le
            · simp [f, hGood, hsel]
              exact hRHSnonneg
          · simp [f, hGood]
            exact hRHSnonneg
        calc
          (∑ z : X.Tuple, π.w z * f (Cz z)) ≤
              ∑ z : X.Tuple, π.w z *
                (∑ a, if bad₀ a then F z a else 0) := by
                  apply Finset.sum_le_sum
                  intro z hz
                  exact mul_le_mul_of_nonneg_left (hRaw z) (π.nonneg z)
          _ = ∑ a, if bad₀ a then m a else 0 := by
                calc
                  _ = ∑ z : X.Tuple, ∑ a,
                        if bad₀ a then π.w z * F z a else 0 := by
                          apply Finset.sum_congr rfl
                          intro z hz
                          rw [Finset.mul_sum]
                          apply Finset.sum_congr rfl
                          intro a ha
                          by_cases hb : bad₀ a <;> simp [hb]
                  _ = ∑ a, ∑ z : X.Tuple,
                        if bad₀ a then π.w z * F z a else 0 := by
                          rw [Finset.sum_comm]
                  _ = ∑ a, if bad₀ a then m a else 0 := by
                          apply Finset.sum_congr rfl
                          intro a ha
                          by_cases hb : bad₀ a
                          · simp [hb, m, Finset.mul_sum]
                          · simp [hb]
          _ ≤ ε := hpostBad
      calc
        (∑ r : Lane_q_s06_ev_a.CentreRest6 X e,
            (Lane_q_s06_ev_a.centreRestLaw6 X H e).w r *
              ∑ z : X.Tuple, (X.tupleLaw H β).w z *
                f (Lane_q_s06_ev_a.centreFromParts6 X e z r)) ≤
            ∑ r : Lane_q_s06_ev_a.CentreRest6 X e,
              (Lane_q_s06_ev_a.centreRestLaw6 X H e).w r * ε := by
                apply Finset.sum_le_sum
                intro r hr
                exact mul_le_mul_of_nonneg_left (hLocal r)
                  ((Lane_q_s06_ev_a.centreRestLaw6 X H e).nonneg r)
        _ = ε := by
          rw [← Finset.sum_mul,
            (Lane_q_s06_ev_a.centreRestLaw6 X H e).sum_eq_one]
          ring
    have hrepr :
        ∑ C : X.Centre, (X.centreLaw H).w C *
          (if X.OddGood H C then starBadMass H C v else 0) =
        ∑ c : X.Loc, ∑ C : X.Centre, (X.centreLaw H).w C *
          (if X.OddGood H C ∧ X.selC H C v = c then starBadMass H C v else 0) := by
      calc
        _ = ∑ C : X.Centre, (X.centreLaw H).w C *
              ∑ c : X.Loc,
                (if X.OddGood H C ∧ X.selC H C v = c then starBadMass H C v else 0) := by
              apply Finset.sum_congr rfl
              intro C hC
              rw [hpoint C, Finset.mul_sum]
        _ = _ := by
          change (∑ C ∈ (Finset.univ : Finset X.Centre),
              (X.centreLaw H).w C *
                ∑ c ∈ (Finset.univ : Finset X.Loc),
                  (if X.OddGood H C ∧ X.selC H C v = c then starBadMass H C v else 0)) =
            ∑ c ∈ (Finset.univ : Finset X.Loc),
              ∑ C ∈ (Finset.univ : Finset X.Centre),
                (X.centreLaw H).w C *
                  (if X.OddGood H C ∧ X.selC H C v = c then starBadMass H C v else 0)
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
    calc
      (X.centreLaw H).expect (fun C =>
          if X.OddGood H C then starBadMass H C v else 0) =
          ∑ c : X.Loc, (X.centreLaw H).expect (fun C =>
            if X.OddGood H C ∧ X.selC H C v = c then starBadMass H C v else 0) := by
            unfold FinProb.expect
            exact hrepr
      _ ≤ ∑ _c : X.Loc, ε := by
            apply Finset.sum_le_sum
            intro c hc
            exact hByC c
      _ = (Fintype.card X.Loc : ℝ) * ε := by simp
  intro Jf hJf
  have hPerHist (H : X.Hist) (hH : X.histLaw.w H ≠ 0)
      (v : CubeVertex n) (hv : IsEvenRole v) :
      ((X.centreLaw H).bind (Jf H)).pr (fun ω =>
        X.OddGood H ω.1 ∧ IsEvenRole v ∧ starFail H ω.1 v ω.2) ≤
          2 * (Fintype.card X.Loc : ℝ) * ε := by
    rw [pr_bind_eq6]
    have hPoint (C : X.Centre) :
        (Jf H C).pr (fun y => X.OddGood H C ∧ IsEvenRole v ∧ starFail H C v y) ≤
          if X.OddGood H C then 2 * starBadMass H C v else 0 := by
      by_cases hGood : X.OddGood H C
      · simpa [hGood, hv] using hPerStar Jf hJf H hH C hGood v
      · simp [FinProb.pr, hGood]
    calc
      (∑ C : X.Centre, (X.centreLaw H).w C *
          (Jf H C).pr (fun y => X.OddGood H C ∧ IsEvenRole v ∧ starFail H C v y)) ≤
        ∑ C : X.Centre, (X.centreLaw H).w C *
          (if X.OddGood H C then 2 * starBadMass H C v else 0) := by
            apply Finset.sum_le_sum
            intro C hC
            exact mul_le_mul_of_nonneg_left (hPoint C) ((X.centreLaw H).nonneg C)
      _ = 2 * (X.centreLaw H).expect (fun C =>
            if X.OddGood H C then starBadMass H C v else 0) := by
            unfold FinProb.expect
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro C hC
            by_cases hGood : X.OddGood H C <;> simp [hGood] <;> ring
      _ ≤ 2 * ((Fintype.card X.Loc : ℝ) * ε) := by
            exact mul_le_mul_of_nonneg_left (hCenterBad H hH v hv) (by norm_num)
      _ = 2 * (Fintype.card X.Loc : ℝ) * ε := by ring
  have hPerV (v : CubeVertex n) :
      (X.fullLaw Jf).pr (fun ω => X.OddGood ω.1 ω.2.1 ∧
        IsEvenRole v ∧ starFail ω.1 ω.2.1 v ω.2.2) ≤
          2 * (Fintype.card X.Loc : ℝ) * ε := by
    by_cases hv : IsEvenRole v
    · change (X.histLaw.bind (fun H => (X.centreLaw H).bind (Jf H))).pr _ ≤ _
      rw [pr_bind_eq6]
      have hPoint (H : X.Hist) :
          X.histLaw.w H *
            ((X.centreLaw H).bind (Jf H)).pr (fun ω =>
              X.OddGood H ω.1 ∧ IsEvenRole v ∧ starFail H ω.1 v ω.2) ≤
          X.histLaw.w H * (2 * (Fintype.card X.Loc : ℝ) * ε) := by
        by_cases hH : X.histLaw.w H = 0
        · simp [hH]
        · exact mul_le_mul_of_nonneg_left (hPerHist H hH v hv)
            (X.histLaw.nonneg H)
      calc
        (∑ H : X.Hist, X.histLaw.w H *
            ((X.centreLaw H).bind (Jf H)).pr (fun ω =>
              X.OddGood H ω.1 ∧ IsEvenRole v ∧ starFail H ω.1 v ω.2)) ≤
          ∑ H : X.Hist, X.histLaw.w H * (2 * (Fintype.card X.Loc : ℝ) * ε) :=
            Finset.sum_le_sum fun H hH => hPoint H
        _ = 2 * (Fintype.card X.Loc : ℝ) * ε := by
          rw [← Finset.sum_mul, X.histLaw.sum_eq_one]
          ring
    · have hEventFalse : ∀ ω : X.Hist × (X.Centre × (OddRole6 n → Fin N)),
          ¬ (X.OddGood ω.1 ω.2.1 ∧ IsEvenRole v ∧ starFail ω.1 ω.2.1 v ω.2.2) := by
        intro ω h
        exact hv h.2.1
      have hzero := pr_zero_of_supp6 (X.fullLaw Jf)
        (fun ω _ => hEventFalse ω)
      rw [hzero]
      positivity
  have hUnion :
      (X.fullLaw Jf).pr (fun ω => X.OddGood ω.1 ω.2.1 ∧
        ∃ v : CubeVertex n, IsEvenRole v ∧ starFail ω.1 ω.2.1 v ω.2.2) ≤
          ∑ v : CubeVertex n, (X.fullLaw Jf).pr (fun ω =>
            X.OddGood ω.1 ω.2.1 ∧ IsEvenRole v ∧ starFail ω.1 ω.2.1 v ω.2.2) := by
    let P := X.fullLaw Jf
    have hUnionFin : ∀ U : Finset (CubeVertex n),
        P.pr (fun ω => X.OddGood ω.1 ω.2.1 ∧
          ∃ v ∈ U, IsEvenRole v ∧ starFail ω.1 ω.2.1 v ω.2.2) ≤
          ∑ v ∈ U, P.pr (fun ω => X.OddGood ω.1 ω.2.1 ∧
            IsEvenRole v ∧ starFail ω.1 ω.2.1 v ω.2.2) := by
      intro U
      induction U using Finset.induction_on with
      | empty => simp [FinProb.pr]
      | @insert v U hv ih =>
          have hEq :
              (fun ω : X.Hist × (X.Centre × (OddRole6 n → Fin N)) =>
                X.OddGood ω.1 ω.2.1 ∧
                ∃ w ∈ insert v U, IsEvenRole w ∧ starFail ω.1 ω.2.1 w ω.2.2) =
              (fun ω : X.Hist × (X.Centre × (OddRole6 n → Fin N)) =>
                (X.OddGood ω.1 ω.2.1 ∧ IsEvenRole v ∧ starFail ω.1 ω.2.1 v ω.2.2) ∨
                (X.OddGood ω.1 ω.2.1 ∧
                  ∃ w ∈ U, IsEvenRole w ∧ starFail ω.1 ω.2.1 w ω.2.2)) := by
            funext ω
            apply propext
            constructor
            · rintro ⟨hGood, w, hw, hvw, hFail⟩
              rcases Finset.mem_insert.mp hw with heq | hw
              · subst w
                exact Or.inl ⟨hGood, hvw, hFail⟩
              · exact Or.inr ⟨hGood, w, hw, hvw, hFail⟩
            · rintro (hleft | hright)
              · rcases hleft with ⟨hGood, hvw, hFail⟩
                exact ⟨hGood, v, Finset.mem_insert_self _ _, hvw, hFail⟩
              · rcases hright with ⟨hGood, w, hw, hvw, hFail⟩
                exact ⟨hGood, w, Finset.mem_insert_of_mem hw, hvw, hFail⟩
          rw [hEq]
          calc
            P.pr (fun ω =>
                (X.OddGood ω.1 ω.2.1 ∧ IsEvenRole v ∧
                    starFail ω.1 ω.2.1 v ω.2.2) ∨
                  (X.OddGood ω.1 ω.2.1 ∧
                    ∃ w ∈ U, IsEvenRole w ∧ starFail ω.1 ω.2.1 w ω.2.2)) ≤
                P.pr (fun ω => X.OddGood ω.1 ω.2.1 ∧ IsEvenRole v ∧
                    starFail ω.1 ω.2.1 v ω.2.2) +
                  P.pr (fun ω => X.OddGood ω.1 ω.2.1 ∧
                    ∃ w ∈ U, IsEvenRole w ∧ starFail ω.1 ω.2.1 w ω.2.2) :=
                      pr_or_le6 P _ _
            _ ≤ P.pr (fun ω => X.OddGood ω.1 ω.2.1 ∧ IsEvenRole v ∧
                    starFail ω.1 ω.2.1 v ω.2.2) +
                  ∑ w ∈ U, P.pr (fun ω => X.OddGood ω.1 ω.2.1 ∧
                    IsEvenRole w ∧ starFail ω.1 ω.2.1 w ω.2.2) :=
                    add_le_add le_rfl ih
            _ = ∑ w ∈ insert v U, P.pr (fun ω => X.OddGood ω.1 ω.2.1 ∧
                    IsEvenRole w ∧ starFail ω.1 ω.2.1 w ω.2.2) := by
                    rw [Finset.sum_insert hv]
    simpa using hUnionFin (Finset.univ : Finset (CubeVertex n))
  calc
    (X.fullLaw Jf).pr (fun ω => X.OddGood ω.1 ω.2.1 ∧
        ∃ v : CubeVertex n, IsEvenRole v ∧ starFail ω.1 ω.2.1 v ω.2.2) ≤
      ∑ v : CubeVertex n, (X.fullLaw Jf).pr (fun ω =>
        X.OddGood ω.1 ω.2.1 ∧ IsEvenRole v ∧ starFail ω.1 ω.2.1 v ω.2.2) := hUnion
    _ ≤ ∑ _v : CubeVertex n,
          2 * (Fintype.card X.Loc : ℝ) * ε := by
            apply Finset.sum_le_sum
            intro v hv
            exact hPerV v
    _ ≤ 1 / 100 := by
          have hCubeCard : Fintype.card (CubeVertex n) = 2 ^ n := by simp
          have hPairNat : Fintype.card (CubeVertex n) * Fintype.card X.Loc ≤
              2 ^ (8 * n) := by
            rw [hCubeCard]
            calc
              2 ^ n * Fintype.card X.Loc ≤ 2 ^ n * 2 ^ (7 * n) :=
                Nat.mul_le_mul_left _ hLocCard
              _ = 2 ^ (8 * n) := by rw [← pow_add]; congr 1; omega
          have hPairReal : (Fintype.card (CubeVertex n) : ℝ) *
              (Fintype.card X.Loc : ℝ) ≤ (2 ^ (8 * n) : ℝ) := by
            exact_mod_cast hPairNat
          have hlog2Upper : Real.log 2 ≤ 1 := by
            have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
            linarith
          have hExpPow : (2 ^ (8 * n) : ℝ) ≤ Real.exp (8 * n) := by
            have hpow : (2 : ℝ) ^ (8 * n) =
                Real.exp ((8 * n : ℝ) * Real.log 2) := by
              rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
              congr 1
              norm_cast <;> ring
            have hcast : (2 ^ (8 * n) : ℝ) = (2 : ℝ) ^ (8 * n) := by norm_cast
            rw [hcast, hpow]
            apply Real.exp_le_exp.mpr
            have hnonneg : 0 ≤ (8 * n : ℝ) := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hlog2Upper hnonneg]
          have hCount : (Fintype.card (CubeVertex n) : ℝ) *
              (Fintype.card X.Loc : ℝ) ≤ Real.exp (8 * n) := hPairReal.trans hExpPow
          have hExpLarge : (200 : ℝ) ≤ Real.exp (72 * n) := by
            have h := Real.add_one_le_exp (72 * (n : ℝ))
            have hnR : (10 ^ 10 : ℝ) ≤ n := by exact_mod_cast hnlarge
            nlinarith
          have hExpNeg : Real.exp (-(72 * (n : ℝ))) ≤ 1 / 200 := by
            rw [Real.exp_neg]
            calc
              (Real.exp (72 * (n : ℝ)))⁻¹ ≤ (200 : ℝ)⁻¹ :=
                (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hExpLarge
              _ = 1 / 200 := by norm_num
          calc
            (∑ _v : CubeVertex n, 2 * (Fintype.card X.Loc : ℝ) * ε) =
                2 * ((Fintype.card (CubeVertex n) : ℝ) *
                  (Fintype.card X.Loc : ℝ)) * ε := by
                    simp [Finset.sum_const, hCubeCard]
                    ring
            _ ≤ 2 * Real.exp (8 * n) * ε := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hCount (by norm_num)) hεpos.le
            _ ≤ 2 * Real.exp (8 * n) *
                  Real.exp (-(4 : ℝ) * Real.log n * n) := by
                  calc
                    2 * Real.exp (8 * n) * ε = (2 * Real.exp (8 * n)) * ε := by ring
                    _ ≤ (2 * Real.exp (8 * n)) *
                        Real.exp (-(4 : ℝ) * Real.log n * n) :=
                      mul_le_mul_of_nonneg_left hεsmall
                        (mul_nonneg (by norm_num) (Real.exp_nonneg _))
                    _ = 2 * Real.exp (8 * n) *
                        Real.exp (-(4 : ℝ) * Real.log n * n) := by ring
            _ = 2 * Real.exp ((8 - 4 * Real.log n) * n) := by
                  rw [show 2 * Real.exp (8 * n) *
                      Real.exp (-(4 : ℝ) * Real.log n * n) =
                      2 * (Real.exp (8 * n) *
                        Real.exp (-(4 : ℝ) * Real.log n * n)) by ring,
                    ← Real.exp_add]
                  congr 2
                  ring
            _ ≤ 2 * Real.exp (-(72 * (n : ℝ))) := by
                  apply mul_le_mul_of_nonneg_left _ (by norm_num)
                  apply Real.exp_le_exp.mpr
                  have hnR : 0 ≤ (n : ℝ) := by positivity
                  nlinarith [hlogn, hnR]
            _ ≤ 1 / 100 := by nlinarith [hExpNeg]

set_option maxHeartbeats 200000

/-- L6.1m (density, 06:826–836): joint density `≤ e^{.4kn}` against the uniform product (prior width
`n^γ + log(2/c₁) = o(n)` per coordinate); `Pr(#{j : x_j ∈ 𝓗} > .8k) ≤ 2^k e^{.4kn}(|𝓗|/N)^{.8k} = o(1)`; the
light mass is at least `.19`; support from the neighbouring kernels at the recomputed star. -/
theorem L6_1m_density (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.HistSupport → X.Step2Supp → X.OddRowBounds → X.EvenDom → X.EvenDensity := by
  classical
  obtain ⟨nT, CT, hT⟩ := (L6_1c_tag γ p₀ K hadm).and (L6_1d_dom γ p₀ K hadm)
  obtain ⟨nW, hW⟩ := Lane_q_s06_ev_b.eventually_width_exp_bound hadm.2.1
  refine ⟨max (max nT nW) 10000, CT, ?_⟩
  intro n N E G M X hL hhist hsupp hrow hdom H C v y hH hv hvalid
  have hnT : nT ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL.1
  have hnW : nW ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL.1
  have hn : 10000 ≤ n := le_trans (le_max_right _ _) hL.1
  have hsteps := hT n N E G M X ⟨hnT, hL.2⟩
  have hstepdom := hsteps.2 hsteps.1
  have hocc := evenTy_occ X v hv
  have hhistory := hhist H hH
  have htests := hhistory.2.2.2.2.1 (X.evenTy v) hocc
  have hkeys := baseSupp_keys X H hhistory.1 (X.typeKeys (X.evenTy v))
  have hkeys₀ := baseSupp_keys X H hhistory.1 { (X.evenTy v).key }
  have htagdom := (hstepdom H (X.evenTy v) hocc hkeys₀ htests).1
  have hk := even_k_pos X (by omega)
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt X.y₀.isLt)
  have hm := hvalid.2.1
  let β := X.evenTy v
  let T := X.Tβ H β
  let U : FinProb (Fin N) := FinProb.uniform Finset.univ ⟨X.y₀, Finset.mem_univ _⟩
  have hU : ∀ a, U.w a = (N : ℝ)⁻¹ := by intro a; simp [U, FinProb.uniform]
  have hraw (z : X.Tuple) :
      (X.tupleLaw H β).w z ≤ T.w z.1 *
        (Real.exp ((4 / 100 : ℝ) * n) / N) ^ X.k := by
    change T.w z.1 * (∏ r : Fin X.k, (X.labelLaw H (reqNames6 β) z.1).w (z.2 r)) ≤ _
    by_cases hz : T.w z.1 = 0
    · simp [hz]
    have hzpos : 0 < T.w z.1 := lt_of_le_of_ne (T.nonneg _) (Ne.symm hz)
    have hΛ : 0 < M.Λ z.1 := by
      have hh := htagdom z.1
      have hp : 0 ≤ (n : ℝ) ^ (d₂ * β.u) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      by_contra h
      have hΛ0 : M.Λ z.1 = 0 := le_antisymm (not_lt.mp h) (M.Λ_nonneg _)
      simp only [hΛ0, mul_zero] at hh
      exact (not_le_of_gt hzpos) hh
    have hmass := (hsupp H β hocc hkeys htests z.1 hzpos).1
    have hpr : (M.μ z.1).pr (fun a => a ∈ X.reqNbhd H (reqNames6 β)) =
        ∑ a ∈ X.reqNbhd H (reqNames6 β), (M.μ z.1).w a := by
      exact Lane_sol_s06_ev_b.pr_mem_set _ _
    have hmass' : (1 / 400 : ℝ) ≤ (M.μ z.1).pr (fun a => a ∈ X.reqNbhd H (reqNames6 β)) := by
      rw [hpr]
      norm_num [c₁, c₀] at hmass ⊢
      exact hmass
    have hp : 0 < (M.μ z.1).pr (fun a => a ∈ X.reqNbhd H (reqNames6 β)) := by linarith
    have hatom (a : Fin N) : (X.labelLaw H (reqNames6 β) z.1).w a ≤
        Real.exp ((4 / 100 : ℝ) * n) / N := by
      calc
        (X.labelLaw H (reqNames6 β) z.1).w a ≤
            (M.μ z.1).w a / (M.μ z.1).pr (fun a => a ∈ X.reqNbhd H (reqNames6 β)) :=
          Lane_q_s06_ev_b.restrictOr6_weight_le _ _ _ _ hp
        _ ≤ (Real.exp ((n : ℝ) ^ γ) / N) / (1 / 400 : ℝ) := by
          exact div_le_div₀ (by positivity) (X.hWidth z.1 hΛ a) (by norm_num) hmass'
        _ = (400 * Real.exp ((n : ℝ) ^ γ)) / N := by ring
        _ ≤ Real.exp ((4 / 100 : ℝ) * n) / N :=
          div_le_div_of_nonneg_right (hW n hnW) hN.le
    apply mul_le_mul_of_nonneg_left _ (T.nonneg _)
    calc
      (∏ r : Fin X.k, (X.labelLaw H (reqNames6 β) z.1).w (z.2 r)) ≤
          ∏ _r : Fin X.k, Real.exp ((4 / 100 : ℝ) * n) / N :=
        Finset.prod_le_prod₀ (fun r _ => (X.labelLaw H (reqNames6 β) z.1).nonneg _) (fun r _ => hatom _)
      _ = (Real.exp ((4 / 100 : ℝ) * n) / N) ^ X.k := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hFnonneg := Fz_nonneg X hrow H hH C v (X.selC H C v)
  let P : FinProb X.Tuple :=
    { w := fun z => (X.tupleLaw H β).w z * X.Fz H C v (X.selC H C v) z y / X.mc H C v y
      nonneg := fun z => div_nonneg (mul_nonneg ((X.tupleLaw H β).nonneg z) (hFnonneg z y)) hm.le
      sum_eq_one := by
        rw [← Finset.sum_div]
        change X.mc H C v y / X.mc H C v y = 1
        exact div_self hm.ne' }
  have hpost (z : X.Tuple) : P.w z ≤ Real.exp ((36 / 100 : ℝ) * X.k * n) * (X.tupleLaw H β).w z := by
    have hF : X.Fz H C v (X.selC H C v) z y ≤
        Real.exp ((36 / 100 : ℝ) * X.k * n) * X.mc H C v y := by
      calc
        X.Fz H C v (X.selC H C v) z y ≤
            Real.exp ((34 / 100 : ℝ) * X.k * n) * X.Qref H C v y := hdom H C v z y hH hv
        _ = Real.exp ((36 / 100 : ℝ) * X.k * n) *
            (Real.exp (-(2 / 100 : ℝ) * X.k * n) * X.Qref H C v y) := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          ring
        _ ≤ Real.exp ((36 / 100 : ℝ) * X.k * n) * X.mc H C v y :=
          mul_le_mul_of_nonneg_left hvalid.2.2 (Real.exp_pos _).le
    change _ / X.mc H C v y ≤ _
    apply (div_le_iff₀ hm).mpr
    nlinarith [mul_le_mul_of_nonneg_left hF ((X.tupleLaw H β).nonneg z)]
  have hPD (i : X.ι) (x : Fin X.k → Fin N) :
      P.w (i, x) ≤ Real.exp ((4 / 10 : ℝ) * X.k * n) * T.w i *
        (FinProb.pi fun _ : Fin X.k => U).w x := by
    calc
      P.w (i, x) ≤ Real.exp ((36 / 100 : ℝ) * X.k * n) * (X.tupleLaw H β).w (i, x) := hpost _
      _ ≤ Real.exp ((36 / 100 : ℝ) * X.k * n) *
          (T.w i * (Real.exp ((4 / 100 : ℝ) * n) / N) ^ X.k) :=
        mul_le_mul_of_nonneg_left (hraw _) (Real.exp_pos _).le
      _ = Real.exp ((4 / 10 : ℝ) * X.k * n) * T.w i *
          (FinProb.pi fun _ : Fin X.k => U).w x := by
        simp only [FinProb.pi, hU, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        have hpower : (Real.exp ((4 / 100 : ℝ) * n) / N) ^ X.k =
            Real.exp ((X.k : ℝ) * ((4 / 100 : ℝ) * n)) * (N : ℝ)⁻¹ ^ X.k := by
          rw [div_eq_mul_inv (Real.exp _) (N : ℝ), mul_pow, ← Real.exp_nat_mul]
        rw [hpower]
        have hexp : Real.exp ((36 / 100 : ℝ) * X.k * n) *
            Real.exp ((X.k : ℝ) * ((4 / 100 : ℝ) * n)) = Real.exp ((4 / 10 : ℝ) * X.k * n) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          _ = (Real.exp ((36 / 100 : ℝ) * X.k * n) * Real.exp ((X.k : ℝ) * ((4 / 100 : ℝ) * n))) *
              T.w i * (N : ℝ)⁻¹ ^ X.k := by ring
          _ = _ := by rw [hexp]
  let Q := P.map Prod.snd
  have hQD := Lane_q_s06_ev_b.map_snd_weight_bound P T (FinProb.pi fun _ : Fin X.k => U)
    (Real.exp ((4 / 10 : ℝ) * X.k * n)) (Real.exp_pos _).le hPD
  have hmarg (a : Fin N) : (∑ x, Q.w x * Lane_sol_s06_ev_b.empirical x a) = X.evenMarg H C v y a := by
    rw [Lane_sol_s06_ev_b.map_snd_empirical]
    rfl
  have hlight := Lane_sol_s06_ev_b.light_mass hk hn U hU Q hQD
  simp_rw [hmarg] at hlight
  change (19 / 100 : ℝ) ≤ ∑ a ∈ Finset.univ.filter (fun a => a ∉ X.heavyLab H C v y),
    X.evenMarg H C v y a at hlight
  have hf (a : Fin N) : 0 ≤ X.evenMarg H C v y a := by
    rw [← hmarg]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (Q.nonneg x) (Lane_sol_s06_ev_b.empirical_nonneg x a)
  have hcap (a : Fin N) (ha : a ∉ X.heavyLab H C v y) :
      X.evenMarg H C v y a ≤ Real.exp ((55 / 100 : ℝ) * n) / N := by
    apply (le_div_iff₀ hN).mpr
    have := not_lt.mp (by simpa [Ctx6.heavyLab] using ha)
    nlinarith
  let f := fun a => if a ∈ X.heavyLab H C v y then 0 else X.evenMarg H C v y a
  have hmassEq : (∑ a, f a) =
      ∑ a ∈ Finset.univ.filter (fun a => a ∉ X.heavyLab H C v y), X.evenMarg H C v y a := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : a ∈ X.heavyLab H C v y <;> simp [f, h]
  have hmass : (19 / 100 : ℝ) ≤ ∑ a, f a := by rw [hmassEq]; exact hlight
  have hmassPos : 0 < ∑ a, f a := by linarith
  have hrowEq (a : Fin N) : X.evenRow H C v y a = f a / ∑ a, f a := by
    rw [Ctx6.evenRow, if_pos hvalid, ← hmassEq]
  have hfLight (a : Fin N) : 0 ≤ f a := by
    dsimp [f]
    split_ifs <;> [rfl; exact hf a]
  have hcapLight (a : Fin N) : f a ≤ Real.exp ((55 / 100 : ℝ) * n) / N := by
    by_cases ha : a ∈ X.heavyLab H C v y
    · simp only [f, if_pos ha]
      positivity
    · simpa only [f, if_neg ha] using hcap a ha
  have hbound (a : Fin N) : X.evenRow H C v y a ≤
      (100 / 19 : ℝ) * (Real.exp ((55 / 100 : ℝ) * n) / N) := by
    rw [hrowEq]
    calc
      f a / (∑ a, f a) ≤ (Real.exp ((55 / 100 : ℝ) * n) / N) / (19 / 100 : ℝ) :=
        div_le_div₀ (by positivity) (hcapLight a) (by norm_num) hmass
      _ = _ := by ring
  refine ⟨?_, ?_, ?_, ?_, hlight⟩
  · intro a
    rw [hrowEq]
    exact div_nonneg (hfLight a) hmassPos.le
  · simp_rw [hrowEq]
    rw [← Finset.sum_div]
    exact div_self hmassPos.ne'
  · intro a ha u hu
    have hmargNZ : X.evenMarg H C v y a ≠ 0 := by
      intro hzero
      simp [Ctx6.evenRow, hvalid, hzero] at ha
    by_contra hhit
    apply hmargNZ
    unfold Ctx6.evenMarg
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hF : X.Fz H C v (X.selC H C v) z y = 0
    · simp [hF]
    have hentries := Fz_hits X hrow H hH C v hv (X.selC H C v) z y hF u hu
    have hempty : (Finset.univ.filter fun r => z.2 r = a) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro r hr heq
      apply hhit
      simpa [heq] using hentries r
    simp [hempty]
  · intro a
    have hh := mul_le_mul_of_nonneg_left (hbound a) hN.le
    have heq : (N : ℝ) * ((100 / 19 : ℝ) * (Real.exp ((55 / 100 : ℝ) * n) / N)) =
        (100 / 19 : ℝ) * Real.exp ((55 / 100 : ℝ) * n) := by
      field_simp
    rw [heq] at hh
    nlinarith [Real.exp_pos ((55 / 100 : ℝ) * n)]

/-- L6.1m (selection, 06:849–853): the forced-centre bounds of Lemma 3.8 (`height_selection_tie`,
`height_selection_positive`) against the position-averaged presence mass. -/
theorem L6_1m_select (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.SelectBound := by
  classical
  obtain ⟨hα0, hαp, hα1, hθ, hAlphaRange, ⟨had⟩⟩ := height_exponents6_admissible p₀ hadm.2.2.1
  let reg : HDRegime (b₀₆ (α₆ p₀)) (b₆ (α₆ p₀)) D₀₆ :=
    .lin (ρ₆ / 4) ⟨by norm_num [ρ₆], by norm_num [ρ₆]⟩
  obtain ⟨c, hc, nH, hheight⟩ := height_selection_positive J₀₆ (b₀₆ (α₆ p₀)) (b₆ (α₆ p₀))
    (σ₆ (α₆ p₀)) (ζ₆ (α₆ p₀)) (θ₆ (α₆ p₀)) (a₆ (α₆ p₀)) cd₆ Cd₆ D₀₆ had reg
  obtain ⟨nErr, hErr⟩ := Lane_sol_s06_ev_b.eventually_height_error c hc
  refine ⟨max (max nH nErr) 1000, 0, ?_⟩
  intro n N E G M X hL H hH v z hv
  have hnH : nH ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL.1
  have hnErr : nErr ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL.1
  have hn : 1000 ≤ n := le_trans (le_max_right _ _) hL.1
  have hnR : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have hreg : reg.ok X.hp.n X.hp.d X.hp.r := by
    change (ρ₆ / 4) * X.code.d ≤ ⌊ρ₆ * n⌋₊ ∧ 4 * ⌊ρ₆ * n⌋₊ ≤ X.code.d
    have hfloor : (⌊ρ₆ * n⌋₊ : ℝ) ≤ ρ₆ * n := Nat.floor_le (by dsimp [ρ₆]; positivity)
    have hfloor' := Nat.lt_floor_add_one (ρ₆ * (n : ℝ))
    have hdL := X.code.d_lower
    have hdU := X.code.d_upper
    norm_num [ρ₆, cd₆, Cd₆] at hfloor hfloor' hdL hdU ⊢
    constructor
    · linarith
    · exact_mod_cast (show 4 * (⌊(1 / 100 : ℝ) * n⌋₊ : ℝ) ≤ X.code.d by linarith)
  have hlam : 0 < X.hp.lam := by
    change 0 < (n : ℝ) ^ J₀₆
    exact Real.rpow_pos_of_pos (by linarith) _
  have hsite : X.site (X.g.L.stateOf v) ∈ X.sites := by
    apply Finset.mem_image.mpr
    refine ⟨X.g.L.stateOf v, ?_, rfl⟩
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  let Es : X.Loc → (X.Loc → Bool) → X.Data X.Loc → X.hp.EligMap := fun id P o =>
    X.elig H ((((P, Function.update o (id, X.evenTy v) z), fun _ => false), fun _ => Equiv.refl _))
  let B : X.Loc → X.Centre → Prop := fun id C => X.EvenGate H (X.withTuple C (id, X.evenTy v) z) v id
  have hB : ∀ id P o A τ, B id (((P, o), A), τ) →
      P id = true ∧ X.hp.Legal P (Es id P o)
        (X.hp.domBall X.sites (X.site (X.g.L.stateOf v)) X.hp.Rlong) ∧
      X.hp.selection X.sites P A (Es id P o) τ (X.site (X.g.L.stateOf v)) = some id := by
    intro id P o A τ hg
    refine ⟨hg.2.1, ?_, ?_⟩
    · exact hg.2.2.2.1
    · exact hg.1
  have hpos : ∀ id, (((X.hp.posLawForced (some id)).prod (X.dataLaw X.Loc H)).prod X.hp.actLaw).pr
      (fun ω => X.hp.Legal ω.1.1 (Es id ω.1.1 ω.1.2)
        (X.hp.domBall X.sites (X.site (X.g.L.stateOf v)) X.hp.Rlong) ∧
        0 < X.hp.height X.sites ω.1.1 ω.2 (Es id ω.1.1 ω.1.2) X.hp.Rlong
          (X.site (X.g.L.stateOf v))) ≤ Real.exp (-(n : ℝ) ^ c) := by
    intro id
    exact hheight X.hp rfl rfl rfl rfl rfl hnH X.code.d_lower X.code.d_upper hreg
      X.sites (X.site (X.g.L.stateOf v)) hsite (some id) (X.dataLaw X.Loc H) (Es id)
  have hsum := Lane_sol_s06_ev_b.forced_selection_sum X.hp hlam X.sites
    (X.site (X.g.L.stateOf v)) hsite (X.dataLaw X.Loc H) Es B hB
    (Real.exp (-(n : ℝ) ^ c)) (Real.exp_pos _).le hpos
  have hlevelBound : X.hp.H ≤ 4 * n ^ 2 := by
    apply Lane_sol_s06_ev_b.topScale_bound (by omega)
    · dsimp [σ₆]
      nlinarith
    · dsimp [ζ₆]
      positivity
  have herror : X.hp.lam * (X.hp.H + 1) * Real.exp (-(n : ℝ) ^ c) ≤ 1 := by
    have hHcast : (X.hp.H : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by exact_mod_cast hlevelBound
    have hlamEq : X.hp.lam = (n : ℝ) ^ (10 : ℕ) := by norm_num [Ctx6.hp, J₀₆]
    have hlevels : (X.hp.H : ℝ) + 1 ≤ 5 * (n : ℝ) ^ 2 := by nlinarith
    calc
      X.hp.lam * (X.hp.H + 1) * Real.exp (-(n : ℝ) ^ c) ≤
          (n : ℝ) ^ (10 : ℕ) * (5 * (n : ℝ) ^ 2) * Real.exp (-(n : ℝ) ^ c) := by
        rw [hlamEq]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlevels (by positivity)) (Real.exp_pos _).le
      _ = 5 * (n : ℝ) ^ (12 : ℕ) * Real.exp (-(n : ℝ) ^ c) := by ring
      _ ≤ 1 := hErr n hnErr
  have hsum' : ∑ id : X.Loc, (X.centreLaw H).pr (B id) ≤ 4 := by
    exact hsum.trans (by linarith)
  simpa only [Lane_sol_s06_ev_b.expect_indicator] using hsum'

namespace Lane_sol_fix_s06mean

theorem oddRow_nonneg (X : Ctx6 γ p₀ K n N E G M) (H : X.Hist) (C : X.Centre)
    (u : CubeVertex n) (a : Fin N) : 0 ≤ X.oddRow H C u a := by
  by_cases hu : X.OddValid H C X.Rlong (X.g.L.stateOf u)
  · rw [← X.oddLaw_eq_row H C u hu a]
    exact (X.oddLaw H C u).nonneg a
  · simp [Ctx6.oddRow, Ctx6.oddRowAt, hu]

theorem Fz_nonneg (X : Ctx6 γ p₀ K n N E G M) (H : X.Hist) (C : X.Centre)
    (v : CubeVertex n) (c : X.Loc) (z : X.Tuple) (y : OddRole6 n → Fin N) :
    0 ≤ X.Fz H C v c z y := by
  unfold Ctx6.Fz
  apply mul_nonneg
  · split_ifs <;> norm_num
  · exact Finset.prod_nonneg fun u _ => oddRow_nonneg X H _ u.1 (y u)

theorem evenMarg_nonneg (X : Ctx6 γ p₀ K n N E G M) (H : X.Hist) (C : X.Centre)
    (v : CubeVertex n) (y : OddRole6 n → Fin N) (a : Fin N) :
    0 ≤ X.evenMarg H C v y a := by
  have hmc : 0 ≤ X.mc H C v y :=
    Finset.sum_nonneg fun z _ => mul_nonneg ((X.tupleLaw H (X.evenTy v)).nonneg z)
      (Fz_nonneg X H C v (X.selC H C v) z y)
  unfold Ctx6.evenMarg
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg
  · exact div_nonneg (mul_nonneg ((X.tupleLaw H (X.evenTy v)).nonneg z)
      (Fz_nonneg X H C v (X.selC H C v) z y)) hmc
  · positivity

/-- Before light-part normalization, retain just the local validity gate. -/
def posteriorMean (X : Ctx6 γ p₀ K n N E G M) (H : X.Hist) (C : X.Centre)
    (v : CubeVertex n) (a : Fin N) : ℝ :=
  (FinProb.pi (fun u : OddRole6 n => X.oddLaw H C u.1)).expect
    (fun y => if X.EvenValid H C v y then (N : ℝ) * X.evenMarg H C v y a else 0)

/-- The density node's retained light mass bounds the cost of normalization by `100/19`. -/
theorem localEvenMean_le_posteriorMean (X : Ctx6 γ p₀ K n N E G M)
    (hDensity : X.EvenDensity) (H : X.Hist) (hH : X.histLaw.w H ≠ 0)
    (C : X.Centre) (v : CubeVertex n) (hv : IsEvenRole v) (a : Fin N) :
    X.localEvenMean H C v a ≤ (100 / 19 : ℝ) * posteriorMean X H C v a := by
  unfold Ctx6.localEvenMean posteriorMean FinProb.expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  have hRow : (N : ℝ) * X.evenRow H C v y a ≤
      (100 / 19 : ℝ) * (if X.EvenValid H C v y then
        (N : ℝ) * X.evenMarg H C v y a else 0) := by
    by_cases hvalid : X.EvenValid H C v y
    · have hmass := (hDensity H C v y hH hv hvalid).2.2.2.2
      have hmarg := evenMarg_nonneg X H C v y a
      have hnum : (if a ∈ X.heavyLab H C v y then 0 else X.evenMarg H C v y a) ≤
          X.evenMarg H C v y a := by
        split_ifs <;> [exact hmarg; exact le_rfl]
      have hrow : X.evenRow H C v y a ≤ (100 / 19 : ℝ) * X.evenMarg H C v y a := by
        rw [Ctx6.evenRow, if_pos hvalid]
        calc
          _ ≤ X.evenMarg H C v y a / (19 / 100 : ℝ) :=
            div_le_div₀ hmarg hnum (by norm_num) hmass
          _ = _ := by ring
      simpa only [if_pos hvalid, mul_assoc, mul_left_comm] using
        mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg N)
    · simp [Ctx6.evenRow, hvalid]
  simpa only [mul_assoc, mul_left_comm] using
    mul_le_mul_of_nonneg_left hRow
      ((FinProb.pi (fun u : OddRole6 n => X.oddLaw H C u.1)).nonneg y)

theorem localEvenMean_nonneg (X : Ctx6 γ p₀ K n N E G M)
    (hDensity : X.EvenDensity) (H : X.Hist) (hH : X.histLaw.w H ≠ 0)
    (C : X.Centre) (v : CubeVertex n) (hv : IsEvenRole v) (a : Fin N) :
    0 ≤ X.localEvenMean H C v a := by
  unfold Ctx6.localEvenMean FinProb.expect
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg ((FinProb.pi (fun u : OddRole6 n => X.oddLaw H C u.1)).nonneg y)
  apply mul_nonneg (Nat.cast_nonneg N)
  by_cases hvalid : X.EvenValid H C v y
  · exact (hDensity H C v y hH hv hvalid).1 a
  · simp [Ctx6.evenRow, hvalid]

end Lane_sol_fix_s06mean

/-- L6.1m (comparison mean, 06:836–853): auxiliary product odd sampling uses probability fillers;
cancellation of the posterior denominator against the data subdensity
(`∫ m_c (F_z dP_c / m_c) dy = dP_c ∫ F_z dy`), rows summing to one bound `∫ F_z dy` by the gate, the selection
bound summed over IDs, and the tuple marginal costs `2/c₁` times the tag mixture; light mass `≥ .19`. -/
theorem L6_1m_mean (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.HistSupport → X.Step2Supp → X.EvenDensity → X.SelectBound → X.EvenMean := by
  refine ⟨2, 0, ?_⟩
  intro n N E G M X _hLarge hHist hSupp hDensity hSelect H hH v a hv
  have hPosterior :
      (X.centreLaw H).expect (fun C => Lane_sol_fix_s06mean.posteriorMean X H C v a) ≤
        (19 / 100 : ℝ) * Cm6 *
          ((N : ℝ) * ∑ i, (X.Tβ H (X.evenTy v)).w i * (M.μ i).w a) := by
    -- Remaining: disintegrate at each selected tuple, cancel m_c, sum the forced-centre
    -- selection bounds, and bound the tuple marginal using HistSupport and Step2Supp.
    sorry
  have hTruncation :
      (X.centreLaw H).expect (fun C => X.localEvenMean H C v a) ≤
        (100 / 19 : ℝ) *
          (X.centreLaw H).expect (fun C => Lane_sol_fix_s06mean.posteriorMean X H C v a) := by
    unfold FinProb.expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro C _
    simpa only [mul_assoc, mul_left_comm] using mul_le_mul_of_nonneg_left
      (Lane_sol_fix_s06mean.localEvenMean_le_posteriorMean X hDensity H hH C v hv a)
      ((X.centreLaw H).nonneg C)
  calc
    _ ≤ _ := hTruncation
    _ ≤ (100 / 19 : ℝ) * ((19 / 100 : ℝ) * Cm6 *
        ((N : ℝ) * ∑ i, (X.Tβ H (X.evenTy v)).w i * (M.μ i).w a)) :=
      mul_le_mul_of_nonneg_left hPosterior (by norm_num)
    _ = _ := by ring

namespace Lane_sol_s06_ev_d

/-- The raw centre moment estimate needed after nonlocal success gates are removed. -/
def RawCentreComparison (X : Ctx6 γ p₀ K n N E G M) : Prop :=
  ∀ H, X.histLaw.w H ≠ 0 → ∀ (U : Finset (CubeVertex n)) (a : Fin N),
    U ⊆ X.evenRoles → U.card ≤ n →
    (∀ v ∈ U, ∀ v' ∈ U, v ≠ v' → X.nearR < X.g.L.residualDist v v') →
      (X.centreLaw H).expect (fun C => ∏ v ∈ U, X.localEvenMean H C v a) ≤
        ∏ v ∈ U, (Cm6 * ((N : ℝ) * ∑ i, (X.Tβ H (X.evenTy v)).w i * (M.μ i).w a))

/-- The original zero-extended product integrand is the filler mean multiplied by the global
all-valid indicator. The repaired `EvenMean` uses the unrestricted filler mean. -/
theorem gatedMean_eq (X : Ctx6 γ p₀ K n N E G M) (H : X.Hist) (C : X.Centre)
    (v : CubeVertex n) (a : Fin N) :
    (∑ y, X.prodOdd H C y * ((N : ℝ) * X.evenRow H C v y a)) =
      if X.AllOddValid H C then X.localEvenMean H C v a else 0 := by
  by_cases hAll : X.AllOddValid H C
  · rw [if_pos hAll]
    unfold Ctx6.localEvenMean FinProb.expect
    apply Finset.sum_congr rfl
    intro y hy
    have hpRow (u : OddRole6 n) :
        (X.oddLaw H C u.1).w (y u) = X.oddRow H C u.1 (y u) :=
      X.oddLaw_eq_row H C u.1 (hAll u.1 u.2) (y u)
    change (∏ u : OddRole6 n, X.oddRow H C u.1 (y u)) *
      ((N : ℝ) * X.evenRow H C v y a) =
      (∏ u : OddRole6 n, (X.oddLaw H C u.1).w (y u)) * ((N : ℝ) * X.evenRow H C v y a)
    simp_rw [hpRow]
  · rw [if_neg hAll]
    have hnot : ¬ ∀ u : OddRole6 n,
        X.OddValid H C X.Rlong (X.g.L.stateOf u.1) := by
      intro hall
      exact hAll (fun u hu => hall ⟨u, hu⟩)
    obtain ⟨u, hu⟩ := not_forall.mp hnot
    apply Finset.sum_eq_zero
    intro y hy
    have hz : X.oddRow H C u.1 (y u) = 0 := by
      simp [Ctx6.oddRow, Ctx6.oddRowAt, hu]
    have hprod : X.prodOdd H C y = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ u) hz
    rw [hprod, zero_mul]

/-- A fully proved reduction from raw centre moments to the joint conclusion. -/
theorem joint_of_rawCentreComparison (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.EvenDensity → RawCentreComparison X → X.EvenJoint := by
  have hp₀ : 0 < p₀ := hadm.2.2.1
  obtain ⟨nNear, hNear⟩ := Filter.eventually_atTop.1
    (Lane_q_s06_ev_d.residual_near_bounds_eventually
      (γ := γ) (p₀ := p₀) (K := K) hp₀)
  obtain ⟨nSquare, hSquare⟩ := Filter.eventually_atTop.1
    Lane_q_s06_ev_d.natSquare_le_powTwo_point025_eventually
  refine ⟨max nNear (max nSquare 100), 1, ?_⟩
  intro n N E G M X hLarge hDensity hRaw
  have hNearDim : nNear ≤ n := le_trans (le_max_left _ _) hLarge.1
  have hBigDim : max nSquare 100 ≤ n := le_trans (le_max_right _ _) hLarge.1
  have hSquareDim : nSquare ≤ n := le_trans (le_max_left _ _) hBigDim
  have hn100 : 100 ≤ n := le_trans (le_max_right _ _) hBigDim
  have hn : 0 < n := by omega
  have hNearData := hNear n hNearDim N E G M X
  have hSquareN := hSquare n hSquareDim
  have hnear : 2 ≤ X.nearR := by
    simp only [Ctx6.nearR]
    omega
  have hstarCard (v : CubeVertex n) : (Lane_q_s06_ev_d.oddStar v).card ≤ n :=
    Lane_q_s06_ev_d.oddStar_card_le X v hn
  have hstarDisjoint (v w : CubeVertex n)
      (hsep : X.nearR < X.g.L.residualDist v w) :
      Disjoint (Lane_q_s06_ev_d.oddStar v) (Lane_q_s06_ev_d.oddStar w) :=
    Lane_q_s06_ev_d.oddStar_disjoint_of_residualDist X v w (lt_of_le_of_lt hnear hsep)
  have hstarImage (v : CubeVertex n) :
      (X.oddNbrs v).image Subtype.val = Lane_q_s06_ev_d.oddStar v := by
    ext u
    simp [Ctx6.oddNbrs, Lane_q_s06_ev_d.oddStar, OddRole6, and_comm]
  have hoddNbrCard (v : CubeVertex n) : (X.oddNbrs v).card ≤ n := by
    calc
      (X.oddNbrs v).card = ((X.oddNbrs v).image Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = (Lane_q_s06_ev_d.oddStar v).card := congrArg Finset.card (hstarImage v)
      _ ≤ n := hstarCard v
  have hoddNbrDisjoint (v w : CubeVertex n)
      (hsep : X.nearR < X.g.L.residualDist v w) : Disjoint (X.oddNbrs v) (X.oddNbrs w) := by
    rw [Finset.disjoint_left]
    intro u huv huw
    have huvRaw : u.1 ∈ Lane_q_s06_ev_d.oddStar v := by
      rw [← hstarImage v]
      exact Finset.mem_image.mpr ⟨u, huv, rfl⟩
    have huwRaw : u.1 ∈ Lane_q_s06_ev_d.oddStar w := by
      rw [← hstarImage w]
      exact Finset.mem_image.mpr ⟨u, huw, rfl⟩
    exact (Finset.disjoint_left.mp (hstarDisjoint v w hsep)) huvRaw huwRaw
  intro Jf hJf H hH U a hU hUcard hsep
  by_cases hUempty : U = ∅
  · subst U
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, mul_one]
    unfold FinProb.expect
    calc
      _ ≤ ∑ ω, ((X.centreLaw H).bind (Jf H)).w ω := by
        apply Finset.sum_le_sum
        intro ω hω
        change ((X.centreLaw H).bind (Jf H)).w ω *
          (if X.OddGood H ω.1 then 1 else 0) ≤ ((X.centreLaw H).bind (Jf H)).w ω
        split_ifs <;> simp [FinProb.nonneg]
      _ = 1 := FinProb.sum_eq_one _
  let S : Finset (OddRole6 n) := U.biUnion X.oddNbrs
  have hScard : S.card ≤ n ^ 2 := by
    calc
      S.card ≤ ∑ v ∈ U, (X.oddNbrs v).card := by
        simpa [S] using (Finset.card_biUnion_le (s := U) (t := X.oddNbrs))
      _ ≤ ∑ v ∈ U, n := Finset.sum_le_sum fun v hv => hoddNbrCard v
      _ = U.card * n := by simp
      _ ≤ n * n := Nat.mul_le_mul_right n hUcard
      _ = n ^ 2 := by ring
  have hScardReal : (S.card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hScard
  have hNlower : (2 : ℝ) ^ n ≤ (N : ℝ) := by simpa using hLarge.2.1
  have hScardJf : (S.card : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) := by
    calc
      (S.card : ℝ) ≤ (n : ℝ) ^ 2 := hScardReal
      _ ≤ ((2 : ℝ) ^ n) ^ (1 / 40 : ℝ) := hSquareN
      _ ≤ (N : ℝ) ^ (1 / 40 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hNlower (by norm_num)
  have hNearProductExp :
      Real.exp ((N : ℝ) ^ (-(1 / 25 : ℝ)) * S.card) ≤ 2 := by
    have hNneg : (N : ℝ) ^ (-(1 / 25 : ℝ)) ≤
        ((2 : ℝ) ^ n) ^ (-(1 / 25 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hNlower (by norm_num)
    have hbase : 0 < (2 : ℝ) ^ n := by positivity
    have hproduct : (N : ℝ) ^ (-(1 / 25 : ℝ)) * S.card ≤
        ((2 : ℝ) ^ n) ^ (-(3 / 200 : ℝ)) := by
      calc
        _ ≤ (N : ℝ) ^ (-(1 / 25 : ℝ)) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hScardReal (by positivity)
        _ ≤ ((2 : ℝ) ^ n) ^ (-(1 / 25 : ℝ)) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hNneg (by positivity)
        _ ≤ ((2 : ℝ) ^ n) ^ (-(1 / 25 : ℝ)) * ((2 : ℝ) ^ n) ^ (1 / 40 : ℝ) :=
          mul_le_mul_of_nonneg_left hSquareN (by positivity)
        _ = ((2 : ℝ) ^ n) ^ (-(3 / 200 : ℝ)) := by
          rw [mul_comm, ← Real.rpow_add hbase]
          congr 1
          norm_num
    have hpowBase : ((2 : ℝ) ^ n) ^ (-(3 / 200 : ℝ)) ≤ 1 / 2 := by
      have hbaseLower : 2 ≤ (2 : ℝ) ^ n := by
        have hnpos : 0 < n := by omega
        have hnat : 2 ≤ 2 ^ n := by
          cases n with
          | zero => omega
          | succ n =>
              simp only [pow_succ]
              have hp : 1 ≤ 2 ^ n := Nat.one_le_pow' _ 1
              omega
        exact_mod_cast hnat
      have hbasePow : ((2 : ℝ) ^ n) ^ (-(3 / 200 : ℝ)) =
          (2 : ℝ) ^ (-(3 / 200 : ℝ) * n) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      have hexp : -(3 / 200 : ℝ) * n ≤ -1 := by
        have hnR : (100 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn100
        nlinarith
      rw [hbasePow]
      calc
        (2 : ℝ) ^ (-(3 / 200 : ℝ) * n) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
        _ = 1 / 2 := by norm_num
    have hlogHalf : (1 / 2 : ℝ) < Real.log 2 := by
      exact lt_trans (by norm_num) Real.log_two_gt_d9
    have harg : (N : ℝ) ^ (-(1 / 25 : ℝ)) * S.card ≤ Real.log 2 :=
      hproduct.trans (hpowBase.trans hlogHalf.le)
    calc
      Real.exp ((N : ℝ) ^ (-(1 / 25 : ℝ)) * S.card) ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.mpr harg
      _ = 2 := Real.exp_log (by norm_num)
  have hEvenRow_local (C : X.Centre) (v : CubeVertex n) (b : Fin N)
      {y y' : OddRole6 n → Fin N}
      (hAgree : ∀ u ∈ X.oddNbrs v, y u = y' u) :
      X.evenRow H C v y b = X.evenRow H C v y' b := by
    have hFz (z : X.Tuple) :
        X.Fz H C v (X.selC H C v) z y = X.Fz H C v (X.selC H C v) z y' := by
      unfold Ctx6.Fz
      have hprod :
          (∏ u ∈ X.oddNbrs v,
            X.oddRow H (X.withTuple C (X.selC H C v, X.evenTy v) z) u.1 (y u)) =
          (∏ u ∈ X.oddNbrs v,
            X.oddRow H (X.withTuple C (X.selC H C v, X.evenTy v) z) u.1 (y' u)) := by
        apply Finset.prod_congr rfl
        intro u hu
        rw [hAgree u hu]
      rw [hprod]
    have hmc : X.mc H C v y = X.mc H C v y' := by
      unfold Ctx6.mc
      apply Finset.sum_congr rfl
      intro z hz
      rw [hFz z]
    have hQ : X.Qref H C v y = X.Qref H C v y' := by
      unfold Ctx6.Qref
      apply Finset.prod_congr rfl
      intro u hu
      rw [hAgree u hu]
    have hvalid : X.EvenValid H C v y = X.EvenValid H C v y' := by
      unfold Ctx6.EvenValid
      rw [hmc, hQ]
    have hMarg (c : Fin N) : X.evenMarg H C v y c = X.evenMarg H C v y' c := by
      unfold Ctx6.evenMarg
      apply Finset.sum_congr rfl
      intro z hz
      rw [hFz z, hmc]
    have hHeavy : X.heavyLab H C v y = X.heavyLab H C v y' := by
      unfold Ctx6.heavyLab
      ext c
      simp [hMarg c]
    unfold Ctx6.evenRow
    rw [hvalid, hHeavy]
    simp_rw [hMarg]
  have hRowNonneg (C : X.Centre) (v : CubeVertex n) (hv : IsEvenRole v)
      (y : OddRole6 n → Fin N) : 0 ≤ (N : ℝ) * X.evenRow H C v y a := by
    by_cases hvalid : X.EvenValid H C v y
    · exact mul_nonneg (Nat.cast_nonneg _) ((hDensity H C v y hH hv hvalid).1 a)
    · simp [Ctx6.evenRow, hvalid]
  have hOddRowMass (C : X.Centre) (u : OddRole6 n) :
      (∑ b : Fin N, X.oddRow H C u.1 b) =
        if X.OddValid H C X.Rlong (X.g.L.stateOf u.1) then 1 else 0 := by
    by_cases hvalid : X.OddValid H C X.Rlong (X.g.L.stateOf u.1)
    · simp only [Ctx6.oddRow, Ctx6.oddRowAt, hvalid, ↓reduceIte]
      cases hmode : X.stMode (X.g.L.stateOf u.1) with
      | low => simpa [hmode] using
          (X.lowRow H (X.pos C) (X.g.L.stateOf u.1)
            (X.actDesc H C X.Rlong (X.g.L.stateOf u.1)) (X.tup C)).sum_eq_one
      | high => simpa [hmode] using
          (X.s3Post H (X.g.L.stateOf u.1)
            (X.actDesc H C X.Rlong (X.g.L.stateOf u.1)) (X.tup C)).sum_eq_one
    · simp [Ctx6.oddRow, Ctx6.oddRowAt, hvalid]
  have hProdOddMass (C : X.Centre) :
      (∑ y : OddRole6 n → Fin N, X.prodOdd H C y) =
        if X.AllOddValid H C then 1 else 0 := by
    classical
    have hsum :
        (∑ y : OddRole6 n → Fin N,
          ∏ u : OddRole6 n, X.oddRow H C u.1 (y u)) =
          ∏ u : OddRole6 n, (∑ b : Fin N, X.oddRow H C u.1 b) := by
      rw [← Fintype.prod_sum]
    rw [show (∑ y : OddRole6 n → Fin N, X.prodOdd H C y) =
        ∑ y : OddRole6 n → Fin N,
          ∏ u : OddRole6 n, X.oddRow H C u.1 (y u) by
      rfl, hsum]
    by_cases hAll : X.AllOddValid H C
    · have hvalid (u : OddRole6 n) :
          X.OddValid H C X.Rlong (X.g.L.stateOf u.1) := hAll u.1 u.2
      simp [hOddRowMass, hvalid, hAll]
    · have hnot : ¬ ∀ u : OddRole6 n,
          X.OddValid H C X.Rlong (X.g.L.stateOf u.1) := by
        intro hall
        exact hAll (by
          intro u hu
          exact hall ⟨u, hu⟩)
      obtain ⟨u, hu⟩ := not_forall.mp hnot
      have hzero : (∑ b : Fin N, X.oddRow H C u.1 b) = 0 := by
        rw [hOddRowMass]
        simp [hu]
      have hprod :
          (∏ u' : OddRole6 n, (∑ b : Fin N, X.oddRow H C u'.1 b)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ u) hzero
      rw [hprod]
      simp [hAll]
  let α := ∀ u : {u : OddRole6 n // u ∈ S}, Fin N
  let project : (OddRole6 n → Fin N) → α := fun y u => y u.1
  let extend : α → OddRole6 n → Fin N := fun o u =>
    if hu : u ∈ S then o ⟨u, hu⟩ else X.y₀
  let g : X.Centre → α → ℝ := fun C o =>
    ∏ v ∈ U, (N : ℝ) * X.evenRow H C v (extend o) a
  let q : X.Centre → α → ℝ := fun C o =>
    Real.exp ((N : ℝ) ^ (-(0.04 : ℝ)) * S.card) *
      ∏ u ∈ S, X.oddRow H C u.1 (extend o u)
  have hOutputComparison (C : X.Centre) (hGood : X.OddGood H C) :
      (Jf H C).expect (fun y => ∏ v ∈ U, (N : ℝ) * X.evenRow H C v y a) ≤
        ∑ o : α, q C o * g C o := by
    have hg : ∀ o, 0 ≤ g C o := by
      intro o
      apply Finset.prod_nonneg
      intro v hv
      exact hRowNonneg C v ((Finset.mem_filter.mp (hU hv)).2) (extend o)
    have hEventEq (o : α) :
        (fun y : OddRole6 n → Fin N => project y = o) =
          (fun y => ∀ u ∈ S, y u = extend o u) := by
      funext y
      apply propext
      constructor
      · intro heq u hu
        have h := congrFun heq ⟨u, hu⟩
        simpa [project, extend, hu] using h
      · intro hall
        funext u
        have h := hall u.1 u.2
        simpa [project, extend, u.2] using h
    have hAtom : ∀ o : α, (Jf H C).pr (fun y => project y = o) ≤ q C o := by
      intro o
      have hJ := hJf H C hH hGood
      rw [hEventEq o]
      have hScardJf' : (S.card : ℝ) ≤ (N : ℝ) ^ (0.025 : ℝ) := by
        simpa only [show (0.025 : ℝ) = 1 / 40 by norm_num] using hScardJf
      exact hJ.2.2 S (extend o) hScardJf'
    have hProjected := Lane_q_s06_ev_d.expect_le_of_atomBound (Jf H C) project (g C) (q C) hg hAtom
    have hLocal (y : OddRole6 n → Fin N) :
        g C (project y) = ∏ v ∈ U, (N : ℝ) * X.evenRow H C v y a := by
      apply Finset.prod_congr rfl
      intro v hv
      have hAgree : ∀ u ∈ X.oddNbrs v, y u = (extend (project y)) u := by
        intro u hu
        have huS : u ∈ S := Finset.mem_biUnion.mpr ⟨v, hv, hu⟩
        simp [extend, project, huS]
      exact congrArg (fun x : ℝ => (N : ℝ) * x)
        (hEvenRow_local C v a (fun u hu => (hAgree u hu).symm))
    have hExpectLocal :
        (Jf H C).expect (fun y => ∏ v ∈ U, (N : ℝ) * X.evenRow H C v y a) =
          (Jf H C).expect (fun y => g C (project y)) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro y hy
      change (Jf H C).w y *
          (∏ v ∈ U, (N : ℝ) * X.evenRow H C v y a) =
        (Jf H C).w y * g C (project y)
      rw [← hLocal y]
    exact (le_of_eq hExpectLocal).trans hProjected
  let p : X.Centre → OddRole6 n → Law N := fun C u =>
    X.oddLaw H C u.1
  let localMean : X.Centre → CubeVertex n → ℝ := fun C v =>
    (FinProb.pi (p C)).expect (fun y => (N : ℝ) * X.evenRow H C v y a)
  have hProductNonneg (C : X.Centre) :
      0 ≤ ∏ v ∈ U, localMean C v := by
    apply Finset.prod_nonneg
    intro v hv
    unfold localMean FinProb.expect
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg ((FinProb.pi (p C)).nonneg y)
        (hRowNonneg C v ((Finset.mem_filter.mp (hU hv)).2) y)
  have hOutputToLocal (C : X.Centre) (hGood : X.OddGood H C) :
      (Jf H C).expect (fun y => ∏ v ∈ U, (N : ℝ) * X.evenRow H C v y a) ≤
        2 * ∏ v ∈ U, localMean C v := by
    let t := Real.exp ((N : ℝ) ^ (-(0.04 : ℝ)) * S.card)
    have hpRow (u : OddRole6 n) (b : Fin N) :
        (p C u).w b = X.oddRow H C u.1 b :=
      X.oddLaw_eq_row H C u.1 (hGood.2.1 u.1 u.2) b
    have hWeight (o : α) :
        q C o = t * (FinProb.pi (fun u : {u : OddRole6 n // u ∈ S} => p C u.1)).w o := by
      change t * (∏ u ∈ S, X.oddRow H C u.1 (extend o u)) =
        t * (∏ u : {u : OddRole6 n // u ∈ S}, (p C u.1).w (o u))
      congr 1
      rw [Finset.univ_eq_attach]
      rw [← Finset.prod_attach S (fun u => X.oddRow H C u.1 (extend o u))]
      apply Finset.prod_congr rfl
      intro u hu
      rw [hpRow]
      simp only [extend, dif_pos u.2]
    have hLocal (y : OddRole6 n → Fin N) :
        g C (project y) = ∏ v ∈ U, (N : ℝ) * X.evenRow H C v y a := by
      apply Finset.prod_congr rfl
      intro v hv
      congr 1
      apply hEvenRow_local
      intro u hu
      have huS : u ∈ S := Finset.mem_biUnion.mpr ⟨v, hv, hu⟩
      simp [extend, project, huS]
    have hProjection :
        (FinProb.pi (p C)).expect (fun y => ∏ v ∈ U, (N : ℝ) * X.evenRow H C v y a) =
        (FinProb.pi (fun u : {u : OddRole6 n // u ∈ S} => p C u.1)).expect (g C) := by
      have heq : (fun y => ∏ v ∈ U, (N : ℝ) * X.evenRow H C v y a) =
          (fun y => g C (project y)) := by
        funext y
        exact (hLocal y).symm
      rw [heq]
      exact FinProb.pi_marginal_expect (p C) S (g C)
    have hFactor :
        (FinProb.pi (p C)).expect (fun y => ∏ v ∈ U, (N : ℝ) * X.evenRow H C v y a) =
          ∏ v ∈ U, localMean C v := by
      apply Lane_q_s06_ev_d.pi_expect_finset_prod_disjoint (p C) U
        (fun v y => (N : ℝ) * X.evenRow H C v y a) X.oddNbrs
      · intro v y y' hAgree
        exact congrArg (fun x : ℝ => (N : ℝ) * x) (hEvenRow_local C v a hAgree)
      · intro v hv w hw hvw
        exact hoddNbrDisjoint v w (hsep v hv w hw hvw)
    have hSum : ∑ o : α, q C o * g C o = t * ∏ v ∈ U, localMean C v := by
      simp_rw [hWeight, mul_assoc]
      rw [← Finset.mul_sum]
      change t * (FinProb.pi (fun u : {u : OddRole6 n // u ∈ S} => p C u.1)).expect (g C) = _
      rw [← hProjection, hFactor]
    have ht : t ≤ 2 := by
      simpa only [t, show (0.04 : ℝ) = 1 / 25 by norm_num] using hNearProductExp
    exact (hOutputComparison C hGood).trans
      (hSum.le.trans (mul_le_mul_of_nonneg_right ht (hProductNonneg C)))
  have hRawReduction :
      ((X.centreLaw H).bind (Jf H)).expect (fun ω => (if X.OddGood H ω.1 then 1 else 0) *
        ∏ v ∈ U, (N : ℝ) * X.evenRow H ω.1 v ω.2 a) ≤
      2 * (X.centreLaw H).expect (fun C => ∏ v ∈ U, localMean C v) := by
    rw [FinProb.bind_expect (X.centreLaw H) (Jf H)
      (fun C y => (if X.OddGood H C then 1 else 0) *
        ∏ v ∈ U, (N : ℝ) * X.evenRow H C v y a)]
    unfold FinProb.expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro C hC
    have hinner :
        (∑ y, (Jf H C).w y * ((if X.OddGood H C then 1 else 0) *
          ∏ v ∈ U, (N : ℝ) * X.evenRow H C v y a)) ≤
        2 * ∏ v ∈ U, localMean C v := by
      by_cases hGood : X.OddGood H C
      · simpa only [FinProb.expect, hGood, if_true, one_mul] using hOutputToLocal C hGood
      · simp only [hGood, if_false, zero_mul, mul_zero, Finset.sum_const_zero]
        exact mul_nonneg (by norm_num) (hProductNonneg C)
    have h := mul_le_mul_of_nonneg_left hinner ((X.centreLaw H).nonneg C)
    simpa only [mul_assoc, mul_left_comm] using h
  have hRawCentreComparison :
      (X.centreLaw H).expect (fun C => ∏ v ∈ U, localMean C v) ≤
        ∏ v ∈ U, (Cm6 * ((N : ℝ) * ∑ i, (X.Tβ H (X.evenTy v)).w i * (M.μ i).w a)) :=
    hRaw H hH U a hU hUcard hsep
  have hBoundsNonneg :
      0 ≤ ∏ v ∈ U, (Cm6 * ((N : ℝ) * ∑ i, (X.Tβ H (X.evenTy v)).w i * (M.μ i).w a)) := by
    apply Finset.prod_nonneg
    intro v hv
    apply mul_nonneg (by norm_num [Cm6])
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Finset.sum_nonneg fun i _ => mul_nonneg ((X.Tβ H (X.evenTy v)).nonneg i) ((M.μ i).nonneg a)
  have hTwo : (2 : ℝ) ≤ 2 ^ U.card := by
    have hcard : 0 < U.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hUempty)
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcard)
  exact hRawReduction.trans ((mul_le_mul_of_nonneg_left hRawCentreComparison (by norm_num)).trans
    (mul_le_mul_of_nonneg_right hTwo hBoundsNonneg))


end Lane_sol_s06_ev_d

namespace Lane_sol_fix_s06mean

/-- The geometric independence step after the global success gate is removed (06:864–865). -/
def CentreMeanFactorization (X : Ctx6 γ p₀ K n N E G M) : Prop :=
  ∀ H, X.histLaw.w H ≠ 0 → ∀ (U : Finset (CubeVertex n)) (a : Fin N),
    U ⊆ X.evenRoles → U.card ≤ n →
    (∀ v ∈ U, ∀ v' ∈ U, v ≠ v' → X.nearR < X.g.L.residualDist v v') →
      (X.centreLaw H).expect (fun C => ∏ v ∈ U, X.localEvenMean H C v a) =
        ∏ v ∈ U, (X.centreLaw H).expect (fun C => X.localEvenMean H C v a)

/-- The repaired first means give precisely the raw moment bound once centre locality is proved. -/
theorem rawCentreComparison_of_mean (X : Ctx6 γ p₀ K n N E G M)
    (hDensity : X.EvenDensity) (hMean : X.EvenMean)
    (hFactor : CentreMeanFactorization X) : Lane_sol_s06_ev_d.RawCentreComparison X := by
  intro H hH U a hU hUcard hsep
  rw [hFactor H hH U a hU hUcard hsep]
  apply Finset.prod_le_prod₀
  · intro v hv
    unfold FinProb.expect
    exact Finset.sum_nonneg fun C _ => mul_nonneg ((X.centreLaw H).nonneg C)
      (localEvenMean_nonneg X hDensity H hH C v (Finset.mem_filter.mp (hU hv)).2 a)
  · intro v hv
    exact hMean H hH v a (Finset.mem_filter.mp (hU hv)).2

end Lane_sol_fix_s06mean

set_option maxHeartbeats 1000000 in
/-- L6.1n (joint comparison, 06:857–868): actual odd-neighbour sets of separated rows are disjoint; the
near-product bound of `JfOK` on at most `n²` outputs; long computations at residual distance `> nearR` read
disjoint centre randomness, so the raw centre integrals factor into the comparison means. -/
theorem L6_1n_joint (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.EvenDensity → X.EvenMean → X.EvenJoint := by
  classical
  apply (Lane_sol_s06_ev_d.joint_of_rawCentreComparison γ p₀ K hadm).mono
  intro n N E G M X hJoint hDensity hMean
  apply hJoint hDensity
  apply Lane_sol_fix_s06mean.rawCentreComparison_of_mean X hDensity hMean
  intro H hH U a hU hUcard hsep
  let R := X.Rlong + X.hp.r + 2 * D₀₆
  let q : CubeVertex n → CubeVertex X.hp.d := fun v => X.site (X.g.L.stateOf v)
  have hs : X.Rshort ≤ X.Rlong := Lane_sol_s06_joint.short_le_long X
  have hnbr (v : CubeVertex n) (hv : IsEvenRole v) (u : OddRole6 n) (hu : u ∈ X.oddNbrs v) :
      X.g.L.stateOf v ∈ X.g.L.stNbr (X.g.L.stateOf u.1) := by
    simp only [ChunkLayout6.stNbr, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u.1, v, u.2, hv, rfl, rfl, (cube n).symm.symm v u.1 (Finset.mem_filter.mp hu).2⟩
  have hnear (v : CubeVertex n) (hv : IsEvenRole v) (u : OddRole6 n) (hu : u ∈ X.oddNbrs v) :
      ∀ b ∈ X.g.L.stNbr (X.g.L.stateOf u.1), _root_.hammingDist (ι := Fin X.hp.d) (X.site b) (q v) ≤ D₀₆ := by
    intro b hb
    exact X.code.nbr_dist _ b hb _ (hnbr v hv u hu)
  have hgate (v : CubeVertex n) (hv : IsEvenRole v) (C C' : X.Centre)
      (hc : Lane_sol_s06_joint.Agree X C C' (q v) R) (c : X.Loc) :
      X.EvenGate H C v c ↔ X.EvenGate H C' v c := by
    have hch : X.choice H C X.Rlong (X.g.L.stateOf v) =
        X.choice H C' X.Rlong (X.g.L.stateOf v) :=
      Lane_sol_s06_joint.choice_congr X H C C' _ _
        (Lane_sol_s06_joint.Agree.recenter X hc (by have hz := Lane_sol_s06_joint.self_dist X (X.site (X.g.L.stateOf v)); dsimp only [q, R]; omega))
    by_cases hsel : X.choice H C X.Rlong (X.g.L.stateOf v) = some c
    · have hpos : X.pos C c = X.pos C' c :=
        (hc c (by have := Lane_sol_s06_joint.choice_mem X H C _ _ c hsel; dsimp [q, R] at *; omega)).1
      have hvalid : (∀ u ∈ X.oddNbrs v, X.OddValid H C X.Rlong (X.g.L.stateOf u.1)) ↔
          (∀ u ∈ X.oddNbrs v, X.OddValid H C' X.Rlong (X.g.L.stateOf u.1)) := by
        apply forall₂_congr
        intro u hu
        exact Lane_sol_s06_joint.oddValid_congr X H C C' _ X.Rlong D₀₆ (q v)
          (hnear v hv u hu) (by simpa [R, two_mul, Nat.add_assoc] using hc)
      have hlegal : X.hp.Legal (X.pos C) (X.elig H C) (X.hp.domBall X.sites (q v) X.hp.Rlong) ↔
          X.hp.Legal (X.pos C') (X.elig H C') (X.hp.domBall X.sites (q v) X.hp.Rlong) := by
        unfold HDParams.Legal
        apply forall₂_congr
        intro b hb
        have hbR := (Finset.mem_filter.mp hb).2
        have hbAgree : Lane_sol_s06_joint.Agree X C C' b (X.hp.r + D₀₆) :=
          Lane_sol_s06_joint.Agree.recenter X hc (by dsimp [R]; change _root_.hammingDist (ι := Fin X.hp.d) b (q v) ≤ X.Rlong at hbR; omega)
        apply forall_congr'
        intro j
        have he := Lane_sol_s06_joint.elig_congr X H C C' b hbAgree j
        unfold HDParams.LegalAt
        rw [← he]
        apply and_congr
        · apply forall₂_congr
          intro ℓ hℓ
          rw [(hbAgree ℓ (by have := Lane_sol_s06_joint.elig_mem X H C b j hℓ; omega)).1]
        · rfl
      have hcounts (l) : X.prosp (X.pos C) (q v) l = X.prosp (X.pos C') (q v) l :=
        Lane_sol_s06_joint.prosp_congr X _ _ _ (fun c hd => (hc c (by dsimp [R]; omega)).1) l
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩
        exact ⟨hch ▸ h1, hpos ▸ h2, hvalid.mp h3, hlegal.mp h4,
          fun l => hcounts l ▸ h5 l⟩
      · rintro ⟨h1, h2, h3, h4, h5⟩
        exact ⟨hch.symm ▸ h1, hpos.symm ▸ h2, hvalid.mpr h3, hlegal.mpr h4,
          fun l => (hcounts l).symm ▸ h5 l⟩
    · have hsel' : X.choice H C' X.Rlong (X.g.L.stateOf v) ≠ some c := by rw [← hch]; exact hsel
      simp [Ctx6.EvenGate, hsel, hsel']
  have hrow (v : CubeVertex n) (hv : IsEvenRole v) (C C' : X.Centre)
      (hc : Lane_sol_s06_joint.Agree X C C' (q v) R) :
      ∀ y b, X.evenRow H C v y b = X.evenRow H C' v y b := by
    have hchoice := Lane_sol_s06_joint.choice_congr X H C C' (X.g.L.stateOf v) X.Rlong
      (Lane_sol_s06_joint.Agree.recenter X hc (by have hz := Lane_sol_s06_joint.self_dist X (X.site (X.g.L.stateOf v)); dsimp only [q, R]; omega))
    have hsel : X.selC H C v = X.selC H C' v := by unfold Ctx6.selC; rw [hchoice]
    have hupdate (c : X.Loc × X.Ty) (z : X.Tuple) :
        Lane_sol_s06_joint.Agree X (X.withTuple C c z) (X.withTuple C' c z) (q v) R := by
      intro ℓ hℓ
      have h := hc ℓ hℓ
      refine ⟨h.1, ?_, h.2.2.1, h.2.2.2⟩
      intro β
      change Function.update (X.tup C) c z (ℓ, β) = Function.update (X.tup C') c z (ℓ, β)
      by_cases he : (ℓ, β) = c
      · simp [he]
      · simp [he, h.2.1 β]
    have hF (z : X.Tuple) (y) : X.Fz H C v (X.selC H C v) z y =
        X.Fz H C' v (X.selC H C' v) z y := by
      rw [← hsel]
      unfold Ctx6.Fz
      rw [hgate v hv _ _ (hupdate _ z)]
      congr 1
      apply Finset.prod_congr rfl
      intro u hu
      have hr := Lane_sol_s06_joint.oddRowAt_congr X H _ _ (X.g.L.stateOf u.1)
        X.Rlong D₀₆ (q v) (hnear v hv u hu) hs
        (by simpa [R, two_mul, Nat.add_assoc] using hupdate (X.selC H C v, X.evenTy v) z)
      exact congrFun hr (y u)
    have hmc (y) : X.mc H C v y = X.mc H C' v y := by
      unfold Ctx6.mc
      simp_rw [hF]
    have hdescs (u : OddRole6 n) (hu : u ∈ X.oddNbrs v) :
        X.descsWith H C (X.g.L.stateOf u.1) (X.selC H C v, X.evenTy v) =
          X.descsWith H C' (X.g.L.stateOf u.1) (X.selC H C' v, X.evenTy v) := by
      let b := X.g.L.stateOf u.1
      rw [← hsel]
      unfold Ctx6.descsWith
      apply Finset.biUnion_congr rfl
      intro j hj
      have hp : X.permAt (X.pos C) b j = X.permAt (X.pos C') b j := by
        funext b'
        unfold Ctx6.permAt
        apply Finset.biUnion_congr rfl
        intro l hl
        apply Lane_sol_s06_joint.prosp_congr X
        intro ℓ hℓ
        have ht := _root_.hammingDist_triangle (ι := Fin X.hp.d) ℓ.1 (X.site b'.1) (q v)
        have hn := hnear v hv u hu b'.1 b'.2
        exact (hc ℓ (by dsimp [R]; omega)).1
      rw [hp]
    have hqref (u : OddRole6 n) (hu : u ∈ X.oddNbrs v) :
        X.qRef H C v u = X.qRef H C' v u := by
      have hd := hdescs u hu
      rw [← hsel] at hd
      have hdata (D : Finset (X.Loc × X.Ty))
          (hD : D ∈ X.descsWith H C (X.g.L.stateOf u.1) (X.selC H C v, X.evenTy v)) :
          ∀ e ∈ D, X.tup C e = X.tup C' e := by
        obtain ⟨j, hj, hD⟩ := Finset.mem_biUnion.mp hD
        have hD := (Finset.mem_filter.mp hD).1
        intro e he
        obtain ⟨b, heb⟩ := Lane_sol_s06_joint.descsIn_mem X _ _ hD he
        obtain ⟨l, hl, heb⟩ := Finset.mem_biUnion.mp heb
        have heb := (Finset.mem_filter.mp heb).2.2.2
        have hn := hnear v hv u hu b.1 b.2
        have ht := _root_.hammingDist_triangle (ι := Fin X.hp.d) e.1.1 (X.site b.1) (q v)
        exact (hc e.1 (by dsimp [R]; omega)).2.1 e.2
      unfold Ctx6.qRef
      dsimp only
      rw [← hsel, ← hd]
      split
      · congr 1
        funext y
        apply Finset.sum_congr rfl
        intro D hD
        have hDel : X.s3Del H (X.g.L.stateOf u.1) D (X.tup C) (X.selC H C v, X.evenTy v) =
            X.s3Del H (X.g.L.stateOf u.1) D (X.tup C') (X.selC H C v, X.evenTy v) := by
          unfold Ctx6.s3Del
          congr 1
          funext ξ
          exact Lane_sol_s06_joint.s3Weight_congr X H _ D _ _ (hdata D hD) _ ξ
        rw [hDel]
      · rfl
    have hQ (y) : X.Qref H C v y = X.Qref H C' v y := by
      unfold Ctx6.Qref
      apply Finset.prod_congr rfl
      intro u hu
      rw [hqref u hu]
    have hmarg (y b) : X.evenMarg H C v y b = X.evenMarg H C' v y b := by
      unfold Ctx6.evenMarg
      simp_rw [hF, hmc]
    have hheavy (y) : X.heavyLab H C v y = X.heavyLab H C' v y := by
      unfold Ctx6.heavyLab
      simp_rw [hmarg]
    intro y b
    have hvalid : X.EvenValid H C v y = X.EvenValid H C' v y := by
      apply propext
      unfold Ctx6.EvenValid
      rw [hsel, hgate v hv C C' hc, hmc, hQ]
    unfold Ctx6.evenRow
    rw [hvalid, hheavy y]
    simp_rw [hmarg]

  have houtput (v : CubeVertex n) (C : X.Centre) (b : Fin N) :
      FinProb.DependsOn (fun y => (N : ℝ) * X.evenRow H C v y b) (X.oddNbrs v) := by
    intro y y' hy
    change (N : ℝ) * X.evenRow H C v y b = (N : ℝ) * X.evenRow H C v y' b
    have hF (z) : X.Fz H C v (X.selC H C v) z y = X.Fz H C v (X.selC H C v) z y' := by
      unfold Ctx6.Fz
      congr 1
      apply Finset.prod_congr rfl
      intro u hu
      rw [hy u hu]
    have hmc : X.mc H C v y = X.mc H C v y' := by unfold Ctx6.mc; simp_rw [hF]
    have hQ : X.Qref H C v y = X.Qref H C v y' := by
      unfold Ctx6.Qref
      apply Finset.prod_congr rfl
      intro u hu
      rw [hy u hu]
    have hmarg (b) : X.evenMarg H C v y b = X.evenMarg H C v y' b := by
      unfold Ctx6.evenMarg
      simp_rw [hF, hmc]
    have hheavy : X.heavyLab H C v y = X.heavyLab H C v y' := by unfold Ctx6.heavyLab; simp_rw [hmarg]
    have hvalid : X.EvenValid H C v y = X.EvenValid H C v y' := by
      apply propext
      unfold Ctx6.EvenValid
      rw [hmc, hQ]
    unfold Ctx6.evenRow
    rw [hvalid, hheavy]
    simp_rw [hmarg]
  have hmean (v : CubeVertex n) (hv : IsEvenRole v) (C C' : X.Centre)
      (hc : Lane_sol_s06_joint.Agree X C C' (q v) R) :
      X.localEvenMean H C v a = X.localEvenMean H C' v a := by
    have hlaw (u : OddRole6 n) (hu : u ∈ X.oddNbrs v) : X.oddLaw H C u.1 = X.oddLaw H C' u.1 := by
      have hvalid := Lane_sol_s06_joint.oddValid_congr X H C C' _ X.Rlong D₀₆ (q v)
        (hnear v hv u hu) (by simpa [R, two_mul, Nat.add_assoc] using hc)
      by_cases hV : X.OddValid H C X.Rlong (X.g.L.stateOf u.1)
      · apply FinProb.ext
        intro b
        rw [Ctx6.oddLaw_eq_row X H C u.1 hV b,
          Ctx6.oddLaw_eq_row X H C' u.1 (hvalid.mp hV) b]
        exact congrFun (Lane_sol_s06_joint.oddRowAt_congr X H C C' _ X.Rlong D₀₆ (q v)
          (hnear v hv u hu) hs (by simpa [R, two_mul, Nat.add_assoc] using hc)) b
      · have hV' : ¬ X.OddValid H C' X.Rlong (X.g.L.stateOf u.1) := fun h => hV (hvalid.mpr h)
        simp [Ctx6.oddLaw, hV, hV']
    unfold Ctx6.localEvenMean
    rw [FinProb.pi_expect_depends _ _ _ (fun _ => X.y₀) (houtput v C a),
      FinProb.pi_expect_depends _ _ _ (fun _ => X.y₀) (houtput v C' a)]
    have hp : (fun u : {u : OddRole6 n // u ∈ X.oddNbrs v} => X.oddLaw H C u.1.1) =
        (fun u : {u : OddRole6 n // u ∈ X.oddNbrs v} => X.oddLaw H C' u.1.1) := by
      funext u
      exact hlaw u.1 u.2
    rw [hp]
    congr 1
    funext y
    rw [hrow v hv C C' hc]
  rw [Lane_sol_s06_joint.centre_expect_eq X H]
  have hdeps (v) (hv : v ∈ U) : FinProb.DependsOn
      (fun ω => X.localEvenMean H (Lane_sol_s06_joint.fromField X ω) v a)
      (Lane_sol_s06_joint.scope X (q v) R) := by
    intro ω ω' hω
    exact hmean v (Finset.mem_filter.mp (hU hv)).2 _ _
      (Lane_sol_s06_joint.agree_of_field X ω ω' (q v) R hω)
  rw [Lane_sol_s06_joint.pi_expect_prod_disjoint (Lane_sol_s06_joint.primitiveLaw X H)
    U (fun v => Lane_sol_s06_joint.scope X (q v) R) _ hdeps]
  · apply Finset.prod_congr rfl
    intro v hv
    exact (Lane_sol_s06_joint.centre_expect_eq X H (fun C => X.localEvenMean H C v a)).symm
  · intro v hv v' hv' hne
    apply Lane_sol_s06_joint.scope_disjoint
    have hres := X.code.residual_dist v v'
    have hsep := hsep v hv v' hv' hne
    have hR : 2 * R ≤ X.nearR := by dsimp [R, Ctx6.nearR, Ctx6.Rlong]; norm_num [D₀₆]; omega
    exact lt_of_le_of_lt hR (lt_of_lt_of_le hsep hres)

set_option maxHeartbeats 1000000
/-- L6.1n (even loads, 06:870–884): close repeats by `H_bin(2ρ) < log 2 − .55` and the cap `10e^{.55n}`; the joint
comparison for separated rows; Lemma 3.6, Markov, the union over labels, and `|A|/N → 0`. -/
theorem L6_1n_loads (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.EvenDensity → X.EvenJoint → X.EvenLoad := by
  have hp₀ : 0 < p₀ := hadm.2.2.1
  obtain ⟨nNear, hNear⟩ := Filter.eventually_atTop.1
    (Lane_q_s06_ev_d.residual_near_bounds_eventually
      (γ := γ) (p₀ := p₀) (K := K) hp₀)
  let Dbar : ℝ := Cm6 * Clh K
  let cutoff : ℝ := 4 * (2 : ℝ) * (Dbar + 1)
  let C₀ : ℝ := cutoff + 1
  have hCm6 : 0 ≤ Cm6 := by norm_num [Cm6]
  have hKpos : 0 < K := hadm.2.2.2
  have hc₁ : 0 < c₁ := by norm_num [c₁, c₀]
  have hClb : 0 ≤ Clb K := by
    unfold Clb
    positivity
  have hClh : 0 ≤ Clh K := by
    unfold Clh
    positivity
  have hDbar : 0 ≤ Dbar := by
    dsimp [Dbar, Cm6]
    positivity
  refine ⟨max nNear 10, C₀, ?_⟩
  intro n N E G M X hLarge hDensity hJoint
  have hNearDim : nNear ≤ n := le_trans (le_max_left _ _) hLarge.1
  have hn10 : 10 ≤ n := le_trans (le_max_right _ _) hLarge.1
  have hn : 0 < n := by omega
  have hNearData := hNear n hNearDim N E G M X
  have hnear : 2 ≤ X.nearR := by
    simp only [Ctx6.nearR]
    omega
  have hrowCap (H : X.Hist) (C : X.Centre) (v : CubeVertex n) (a : Fin N)
      (hH : X.histLaw.w H ≠ 0) (hv : IsEvenRole v) (y : OddRole6 n → Fin N)
      (hvalid : X.EvenValid H C v y) :
      (N : ℝ) * X.evenRow H C v y a ≤ 10 * Real.exp ((55 / 100) * n) := by
    exact (hDensity H C v y hH hv hvalid).2.2.2.1 a
  have hRadiusEq : X.nearR = Lane_q_s06_ev_d.separationRadius X := rfl
  let near : CubeVertex n → Finset (CubeVertex n) := fun v =>
    Finset.univ.filter fun w => X.g.L.residualDist v w ≤ X.nearR
  let f : ℝ := Real.exp (-(56 / 100 : ℝ) * n)
  let L : ℝ := 10 * Real.exp ((55 / 100 : ℝ) * n)
  have hnearCard (v : CubeVertex n) :
      ((near v).card : ℝ) ≤ f * Fintype.card (CubeVertex n) := by
    have h := (hNearData v).1
    dsimp [near, f]
    simpa [hRadiusEq] using h
  have hnearSelf (v : CubeVertex n) : v ∈ near v := by
    simp [near, ChunkLayout6.residualDist]
  have hsmall : (n : ℝ) * f * L ≤ 1 := by
    simpa [f, L] using (hNearData (fun _ : Fin n => false)).2
  intro Jf hJf
  let mixGood : X.Hist → Prop := fun H => ∀ a, X.mixAvg H a ≤ Clh K
  have hfixed (H : X.Hist) (hH : X.histLaw.w H ≠ 0) :
      ((X.centreLaw H).bind (Jf H)).pr (fun ω =>
        X.OddGood H ω.1 ∧ mixGood H ∧
          (∀ v : CubeVertex n, IsEvenRole v → X.EvenValid H ω.1 v ω.2) ∧
          ∃ a, 1 < ∑ v ∈ X.evenRoles, X.evenRow H ω.1 v ω.2 a) ≤ 1 / 100 := by
    by_cases hmix : mixGood H
    · let Ω := X.Centre × (OddRole6 n → Fin N)
      let P : FinProb Ω := (X.centreLaw H).bind (Jf H)
      let succ : Finset Ω := Finset.univ.filter fun ω => X.OddGood H ω.1
      let Z : CubeVertex n → Fin N → Ω → ℝ := fun v a ω =>
        if IsEvenRole v then (N : ℝ) * X.evenRow H ω.1 v ω.2 a else 0
      let d : CubeVertex n → Fin N → ℝ := fun v a =>
        if IsEvenRole v then Cm6 * ((N : ℝ) *
          ∑ i, (X.Tβ H (X.evenTy v)).w i * (M.μ i).w a) else 0
      have hZ0 : ∀ v a ω, 0 ≤ Z v a ω := by
        intro v a ω
        by_cases hv : IsEvenRole v
        · by_cases hvalid : X.EvenValid H ω.1 v ω.2
          · simpa [Z, hv] using
              mul_nonneg (Nat.cast_nonneg _) ((hDensity H ω.1 v ω.2 hH hv hvalid).1 a)
          · simp [Z, hv, Ctx6.evenRow, hvalid]
        · simp [Z, hv]
      have hZL : ∀ v a ω, ω ∈ succ → Z v a ω ≤ L := by
        intro v a ω hω
        by_cases hv : IsEvenRole v
        · by_cases hvalid : X.EvenValid H ω.1 v ω.2
          · simpa [Z, hv] using hrowCap H ω.1 v a hH hv ω.2 hvalid
          · simp [Z, hv, Ctx6.evenRow, hvalid, L]
            positivity
        · simp [Z, hv, L]
          positivity
      have hd : ∀ v a, 0 ≤ d v a := by
        intro v a
        by_cases hv : IsEvenRole v
        · simp only [d, hv, if_true]
          apply mul_nonneg
          · norm_num [Cm6]
          · apply mul_nonneg
            · exact Nat.cast_nonneg N
            · apply Finset.sum_nonneg
              intro i hi
              exact mul_nonneg ((X.Tβ H (X.evenTy v)).nonneg i) ((M.μ i).nonneg a)
        · simp [d, hv]
      let v0 : CubeVertex n := fun _ => false
      have hv0 : IsEvenRole v0 := by simp [IsEvenRole, v0]
      have hv0even : v0 ∈ X.evenRoles := by simp [Ctx6.evenRoles, v0, hv0]
      have hEvenCardPos : 0 < (X.evenRoles.card : ℝ) :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨v0, hv0even⟩)
      have hCubeCardPos : 0 < (Fintype.card (CubeVertex n) : ℝ) := by positivity
      have hEvenCardLe : (X.evenRoles.card : ℝ) ≤ Fintype.card (CubeVertex n) :=
        Nat.cast_le.mpr (Finset.card_le_univ X.evenRoles)
      have hevenTy (v : CubeVertex n) : X.evenTy v = X.evenType v := by
        unfold Ctx6.evenTy Ctx6.evenType Ctx6.stType ChunkLayout6.stType
        rw [X.facts.key_eq v, X.facts.sign_eq v, X.facts.flippable_eq v, X.facts.severity_eq v]
      have hmean : ∀ a, (Fintype.card (CubeVertex n) : ℝ)⁻¹ *
          ∑ v, d v a ≤ Dbar := by
        intro a
        let g : CubeVertex n → ℝ := fun v =>
          (N : ℝ) * ∑ i, (X.Tβ H (X.evenTy v)).w i * (M.μ i).w a
        have hsumd : ∑ v, d v a = Cm6 * ∑ v ∈ X.evenRoles, g v := by
          calc
            ∑ v, d v a = ∑ v, Cm6 * (if IsEvenRole v then g v else 0) := by
              apply Finset.sum_congr rfl
              intro v hv
              by_cases hrole : IsEvenRole v <;> simp [d, g, hrole]
            _ = Cm6 * ∑ v, if IsEvenRole v then g v else 0 := by rw [Finset.mul_sum]
            _ = Cm6 * ∑ v ∈ X.evenRoles, g v := by simp [Ctx6.evenRoles, Finset.sum_filter]
        have hMix : 0 ≤ X.mixAvg H a := by
          unfold Ctx6.mixAvg
          apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
          apply Finset.sum_nonneg
          intro v hv
          exact mul_nonneg (Nat.cast_nonneg N) <| Finset.sum_nonneg fun i hi =>
            mul_nonneg ((X.Tβ H (X.evenType v)).nonneg i) ((M.μ i).nonneg a)
        have hsumMix : ∑ v ∈ X.evenRoles, g v =
            (X.evenRoles.card : ℝ) * X.mixAvg H a := by
          have hcardne : (X.evenRoles.card : ℝ) ≠ 0 := hEvenCardPos.ne'
          have hsumType : ∑ v ∈ X.evenRoles, g v =
              ∑ v ∈ X.evenRoles, (N : ℝ) *
                ∑ i, (X.Tβ H (X.evenType v)).w i * (M.μ i).w a := by
            apply Finset.sum_congr rfl
            intro v hv
            simp [g, hevenTy v]
          calc
            ∑ v ∈ X.evenRoles, g v = (X.evenRoles.card : ℝ) *
                ((X.evenRoles.card : ℝ)⁻¹ * ∑ v ∈ X.evenRoles, g v) := by
                  field_simp [hcardne]
            _ = (X.evenRoles.card : ℝ) * X.mixAvg H a := by
              rw [hsumType]
              simp [Ctx6.mixAvg]
        rw [hsumd, hsumMix]
        have hratio : (X.evenRoles.card : ℝ) / Fintype.card (CubeVertex n) ≤ 1 :=
          (div_le_one₀ hCubeCardPos).2 hEvenCardLe
        have hmean' : (Fintype.card (CubeVertex n) : ℝ)⁻¹ *
            (Cm6 * ((X.evenRoles.card : ℝ) * X.mixAvg H a)) =
              Cm6 * ((X.evenRoles.card : ℝ) / Fintype.card (CubeVertex n)) * X.mixAvg H a := by
          field_simp [ne_of_gt hCubeCardPos]
        rw [hmean']
        calc
          Cm6 * ((X.evenRoles.card : ℝ) / Fintype.card (CubeVertex n)) * X.mixAvg H a =
              Cm6 * (((X.evenRoles.card : ℝ) / Fintype.card (CubeVertex n)) * X.mixAvg H a) := by ring
          _ ≤ Cm6 * (1 * X.mixAvg H a) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hratio hMix) hCm6
          _ = Cm6 * X.mixAvg H a := by ring
          _ ≤ Dbar := by
            dsimp [Dbar]
            exact mul_le_mul_of_nonneg_left (hmix a) hCm6
      have hjointMoment : ∀ a (m : ℕ), m ≤ n → ∀ s : Fin m → CubeVertex n,
          (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
            ∑ ω ∈ succ, P.w ω * ∏ i, Z (s i) a ω ≤
              (2 : ℝ) ^ m * ∏ i, d (s i) a := by
        intro a m hm s hsep
        by_cases hall : ∀ i, IsEvenRole (s i)
        · let Uset : Finset (CubeVertex n) := Finset.univ.image s
          have hsinj : Function.Injective s := by
            intro i j hij
            by_contra hne
            rcases lt_or_gt_of_ne hne with hij' | hji'
            · have hbad := hsep j i hij'
              have hmem : s j ∈ near (s i) := by rw [← hij]; exact hnearSelf (s i)
              exact hbad hmem
            · have hbad := hsep i j hji'
              have hmem : s i ∈ near (s j) := by rw [hij]; exact hnearSelf (s j)
              exact hbad hmem
          have hcard : Uset.card = m := by
            calc
              Uset.card = (Finset.univ.image s).card := rfl
              _ = Finset.univ.card := Finset.card_image_of_injective _ hsinj
              _ = m := by simp
          have hU : Uset ⊆ X.evenRoles := by
            intro v hv
            rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall i⟩
          have hfarNotNear {x y : CubeVertex n} (hxy : x ∉ near y) :
              X.nearR < X.g.L.residualDist y x := by
            have hxy' : ¬ X.g.L.residualDist y x ≤ X.nearR := by
              simpa [near] using hxy
            exact Nat.lt_of_not_ge hxy'
          have hsepSet : ∀ v ∈ Uset, ∀ w ∈ Uset, v ≠ w →
              X.nearR < X.g.L.residualDist v w := by
            intro v hv w hw hne
            rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
            rcases Finset.mem_image.mp hw with ⟨j, hj, rfl⟩
            have hij : i ≠ j := by
              intro hEq
              apply hne
              subst j
              rfl
            rcases lt_or_gt_of_ne hij with hij' | hji'
            · exact hfarNotNear (hsep j i hij')
            · have hfar := hfarNotNear (hsep i j hji')
              rw [Lane_q_s06_ev_d.residualDist_comm X (s j) (s i)] at hfar
              exact hfar
          have hcardLe : Uset.card ≤ n := by rw [hcard]; exact hm
          have hJointApplied := hJoint Jf hJf H hH Uset a hU hcardLe hsepSet
          have hprodD : ∏ v ∈ Uset, d v a = ∏ i, d (s i) a := by
            change (∏ v ∈ Finset.univ.image s, d v a) = ∏ i, d (s i) a
            exact Finset.prod_image (s := Finset.univ) (g := s) (by
              intro i hi j hj heq
              exact hsinj heq)
          have hprodRow : ∀ ω : Ω,
              ∏ i, Z (s i) a ω = ∏ v ∈ Uset,
                (N : ℝ) * X.evenRow H ω.1 v ω.2 a := by
            intro ω
            calc
              ∏ i, Z (s i) a ω = ∏ i, (N : ℝ) * X.evenRow H ω.1 (s i) ω.2 a := by
                apply Finset.prod_congr rfl
                intro i hi
                simp [Z, hall i]
              _ = ∏ v ∈ Uset, (N : ℝ) * X.evenRow H ω.1 v ω.2 a := by
                symm
                change (∏ v ∈ Finset.univ.image s, (N : ℝ) * X.evenRow H ω.1 v ω.2 a) = _
                exact Finset.prod_image (s := Finset.univ) (g := s) (by
                  intro i hi j hj heq
                  exact hsinj heq)
          have hsumFilter :
              ∑ ω ∈ succ, P.w ω * ∏ i, Z (s i) a ω =
                ∑ ω, if X.OddGood H ω.1 then P.w ω * ∏ i, Z (s i) a ω else 0 := by
            simp [succ, Finset.sum_filter]
          have hsumExpect :
              ∑ ω ∈ succ, P.w ω * ∏ i, Z (s i) a ω =
                P.expect (fun ω => (if X.OddGood H ω.1 then 1 else 0) *
                  ∏ v ∈ Uset, (N : ℝ) * X.evenRow H ω.1 v ω.2 a) := by
            unfold FinProb.expect
            rw [hsumFilter]
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hg : X.OddGood H ω.1
            · simp [hg, hprodRow ω]
            · simp [hg]
          have hfactor :
              ∏ v ∈ Uset,
                (Cm6 * ((N : ℝ) * ∑ i, (X.Tβ H (X.evenTy v)).w i * (M.μ i).w a)) =
                ∏ v ∈ Uset, d v a := by
            apply Finset.prod_congr rfl
            intro v hv
            have hrole : IsEvenRole v := by
              rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
              exact hall i
            simp [d, hrole]
          calc
            ∑ ω ∈ succ, P.w ω * ∏ i, Z (s i) a ω =
                P.expect (fun ω => (if X.OddGood H ω.1 then 1 else 0) *
                  ∏ v ∈ Uset, (N : ℝ) * X.evenRow H ω.1 v ω.2 a) := hsumExpect
            _ ≤ 2 ^ Uset.card *
                ∏ v ∈ Uset,
                  (Cm6 * ((N : ℝ) * ∑ i, (X.Tβ H (X.evenTy v)).w i * (M.μ i).w a)) :=
              hJointApplied
            _ = (2 : ℝ) ^ m * ∏ i, d (s i) a := by rw [hcard, hfactor, hprodD]
        · obtain ⟨i, hi⟩ := not_forall.mp hall
          have hprodZero (ω : Ω) : ∏ j, Z (s j) a ω = 0 := by
            exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Z, hi])
          have hleft : ∑ ω ∈ succ, P.w ω * ∏ i, Z (s i) a ω = 0 := by
            apply Finset.sum_eq_zero
            intro ω hω
            simp [hprodZero]
          have hright : 0 ≤ (2 : ℝ) ^ m * ∏ i, d (s i) a := by
            apply mul_nonneg (by positivity)
            apply Finset.prod_nonneg
            intro i hi
            exact hd (s i) a
          rw [hleft]
          exact hright
      have hlabels : (Fintype.card (Fin N) : ℝ) ≤ (n : ℝ) * 2 ^ n := by
        have hN := hLarge.2.2
        have hNr : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by exact_mod_cast hN
        simpa using hNr
      have hSC := HypercubeRamsey.scatteredMoments_union_labels P succ Z hZ0 L
        (by positivity) hZL near hnearSelf f (by positivity) hnearCard n (by omega)
        (2 : ℝ) Dbar (by norm_num) hDbar d hd hmean hjointMoment hsmall hlabels
      have hpow100 := Lane_q_s06_ev_d.pow_two_dominates_100 hn10
      have hpow100R : (100 : ℝ) * n ≤ (2 : ℝ) ^ n := by exact_mod_cast hpow100
      have hrateEq : (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n =
          (n : ℝ) / (2 : ℝ) ^ n := by
        have hpow : (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
          rw [← mul_pow]
          norm_num
        have hhalf : (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n := by
          rw [div_pow]
          simp
        calc
          (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n =
              (n : ℝ) * ((2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) := by ring
          _ = (n : ℝ) * (1 / 2 : ℝ) ^ n := by rw [hpow]
          _ = (n : ℝ) / (2 : ℝ) ^ n := by rw [hhalf, div_eq_mul_inv]; ring
      have hrate : (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n ≤ 1 / 100 := by
        rw [hrateEq]
        apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ n)).2
        nlinarith [hpow100R]
      let average : Fin N → Ω → ℝ := fun a ω =>
        (Fintype.card (CubeVertex n) : ℝ)⁻¹ * ∑ v, Z v a ω
      have hSCprob : P.pr (fun ω => ω ∈ succ ∧ ∃ a, cutoff < average a ω) ≤
          (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n := by
        simpa [FinProb.pr, average] using hSC
      have hNpos : 0 < (N : ℝ) := by
        have hC₀ : 0 < C₀ := by dsimp [C₀, cutoff, Dbar]; positivity
        have hpowPos : 0 < (2 : ℝ) ^ n := by positivity
        exact lt_of_lt_of_le (mul_pos hC₀ hpowPos) hLarge.2.1
      have hratioPos : 0 < (N : ℝ) / (2 : ℝ) ^ n := div_pos hNpos (by positivity)
      have hhostRatio : cutoff < (N : ℝ) / (2 : ℝ) ^ n := by
        have hC₀le : cutoff < C₀ := by dsimp [C₀]; linarith
        have hlargeRatio : C₀ ≤ (N : ℝ) / (2 : ℝ) ^ n :=
          (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ n)).2 hLarge.2.1
        exact lt_of_lt_of_le hC₀le hlargeRatio
      have hsumZ (a : Fin N) (ω : Ω) :
          ∑ v, Z v a ω = (N : ℝ) * ∑ v ∈ X.evenRoles, X.evenRow H ω.1 v ω.2 a := by
        calc
          ∑ v, Z v a ω = ∑ v, if IsEvenRole v then
              (N : ℝ) * X.evenRow H ω.1 v ω.2 a else 0 := by
                apply Finset.sum_congr rfl
                intro v hv
                by_cases hv' : IsEvenRole v <;> simp [Z, hv']
          _ = ∑ v ∈ X.evenRoles, (N : ℝ) * X.evenRow H ω.1 v ω.2 a := by
                simp [Ctx6.evenRoles, Finset.sum_filter]
          _ = (N : ℝ) * ∑ v ∈ X.evenRoles, X.evenRow H ω.1 v ω.2 a := by
                rw [Finset.mul_sum]
      have havgEq (a : Fin N) (ω : Ω) :
          average a ω = (N : ℝ) / (2 : ℝ) ^ n *
            ∑ v ∈ X.evenRoles, X.evenRow H ω.1 v ω.2 a := by
        dsimp [average]
        rw [hsumZ, show (Fintype.card (CubeVertex n) : ℝ) = (2 : ℝ) ^ n by simp]
        field_simp [ne_of_gt (show (0 : ℝ) < (2 : ℝ) ^ n by positivity)]
      have hsubset : ∀ ω, (X.OddGood H ω.1 ∧ mixGood H ∧
          (∀ v : CubeVertex n, IsEvenRole v → X.EvenValid H ω.1 v ω.2) ∧
          ∃ a, 1 < ∑ v ∈ X.evenRoles, X.evenRow H ω.1 v ω.2 a) →
            ω ∈ succ ∧ ∃ a, cutoff < average a ω := by
        intro ω hbad
        rcases hbad with ⟨hgood, _hmix, _hvalid, ⟨a, hload⟩⟩
        have hsucc : ω ∈ succ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood⟩
        refine ⟨hsucc, a, ?_⟩
        have hloadFactor : (N : ℝ) / (2 : ℝ) ^ n <
            (N : ℝ) / (2 : ℝ) ^ n *
              ∑ v ∈ X.evenRoles, X.evenRow H ω.1 v ω.2 a := by
          calc
            (N : ℝ) / (2 : ℝ) ^ n =
                (N : ℝ) / (2 : ℝ) ^ n * 1 := by ring
            _ < _ := mul_lt_mul_of_pos_left hload hratioPos
        calc
          cutoff < (N : ℝ) / (2 : ℝ) ^ n := hhostRatio
          _ < average a ω := by rw [havgEq]; exact hloadFactor
      have hconditional : P.pr (fun ω => X.OddGood H ω.1 ∧ mixGood H ∧
          (∀ v : CubeVertex n, IsEvenRole v → X.EvenValid H ω.1 v ω.2) ∧
          ∃ a, 1 < ∑ v ∈ X.evenRoles, X.evenRow H ω.1 v ω.2 a) ≤ 1 / 100 := by
        calc
          _ ≤ P.pr (fun ω => ω ∈ succ ∧ ∃ a, cutoff < average a ω) :=
            pr_mono6 P hsubset
          _ ≤ (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n := hSCprob
          _ ≤ 1 / 100 := hrate
      exact hconditional
    · have hz : ((X.centreLaw H).bind (Jf H)).pr (fun ω =>
          X.OddGood H ω.1 ∧ mixGood H ∧
            (∀ v : CubeVertex n, IsEvenRole v → X.EvenValid H ω.1 v ω.2) ∧
            ∃ a, 1 < ∑ v ∈ X.evenRoles, X.evenRow H ω.1 v ω.2 a) = 0 := by
        apply pr_zero_of_supp6
        intro ω hω hbad
        exact hmix hbad.2.1
      rw [hz]
      norm_num
  change (X.histLaw.bind (fun H => (X.centreLaw H).bind (Jf H))).pr
      (fun ω => X.OddGood ω.1 ω.2.1 ∧ mixGood ω.1 ∧
        (∀ v : CubeVertex n, IsEvenRole v → X.EvenValid ω.1 ω.2.1 v ω.2.2) ∧
        ∃ a, 1 < ∑ v ∈ X.evenRoles, X.evenRow ω.1 ω.2.1 v ω.2.2 a) ≤ 1 / 100
  rw [pr_bind_eq6]
  calc
    (∑ H, X.histLaw.w H *
        ((X.centreLaw H).bind (Jf H)).pr (fun ω =>
          X.OddGood H ω.1 ∧ mixGood H ∧
            (∀ v : CubeVertex n, IsEvenRole v → X.EvenValid H ω.1 v ω.2) ∧
            ∃ a, 1 < ∑ v ∈ X.evenRoles, X.evenRow H ω.1 v ω.2 a)) ≤
      ∑ H, X.histLaw.w H * (1 / 100 : ℝ) := by
        apply Finset.sum_le_sum
        intro H hH
        by_cases hzero : X.histLaw.w H = 0
        · simp [hzero]
        · exact mul_le_mul_of_nonneg_left (hfixed H hzero) (X.histLaw.nonneg H)
    _ = 1 / 100 := by
      rw [← Finset.sum_mul, X.histLaw.sum_eq_one]
      ring

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
