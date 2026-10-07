import HypercubeRamsey.S06.OddLoads
import HypercubeRamsey.S06.Prob
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.S06.EvenRows_q_s06_even
import HypercubeRamsey.S06.EvenRows_q_s06_ev_b
import HypercubeRamsey.S06.EvenRows_sol_s06_ev_b
import HypercubeRamsey.S06.EvenRows_select_sol_s06_ev_b
import HypercubeRamsey.S06.EvenRows_q_s06_ev_d

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

/-- L6.1m (comparison mean, 06:836–853): cancellation of the posterior denominator against the data subdensity
(`∫ m_c (F_z dP_c / m_c) dy = dP_c ∫ F_z dy`), rows summing to one bound `∫ F_z dy` by the gate, the selection
bound summed over IDs, and the tuple marginal costs `2/c₁` times the tag mixture; light mass `≥ .19`. -/
theorem L6_1m_mean (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.HistSupport → X.Step2Supp → X.EvenDensity → X.SelectBound → X.EvenMean := by
  sorry

/-- L6.1n (joint comparison, 06:857–868): actual odd-neighbour sets of separated rows are disjoint; the
near-product bound of `JfOK` on at most `n²` outputs; long computations at residual distance `> nearR` read
disjoint centre randomness, so the raw centre integrals factor into the comparison means. -/
theorem L6_1n_joint (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.EvenDensity → X.EvenMean → X.EvenJoint := by
  have hp₀ : 0 < p₀ := hadm.2.2.1
  obtain ⟨nNear, hNear⟩ := Filter.eventually_atTop.1
    (Lane_q_s06_ev_d.residual_near_bounds_eventually
      (γ := γ) (p₀ := p₀) (K := K) hp₀)
  obtain ⟨nSquare, hSquare⟩ := Filter.eventually_atTop.1
    Lane_q_s06_ev_d.natSquare_le_powTwo_point025_eventually
  refine ⟨max nNear (max nSquare 100), 1, ?_⟩
  intro n N E G M X hLarge hDensity hMean
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
  sorry

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
