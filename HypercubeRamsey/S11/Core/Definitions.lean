import HypercubeRamsey.Framework.OneShot
import HypercubeRamsey.Framework.PartC
import HypercubeRamsey.Tools.CubeGeometry

/-!
# Proposition 11.1: parameters, the slice experiment, compatibility and the outer moment

Source: `refs/openai-paper/sections/11-jump-to-large-bias-only-at-linear-budget.tex` (cited `11:line`);
blueprint `research/blueprint/PART-B.md` §3.11.  Every object is an explicit finite formula:

* parameters `h = ⌊n^.1⌋` (`hIn`), `k = ⌈n^.2⌉` (`kTup`), `g = n^{-.01}` (`gS`), `b_* = n^{-.95}` (`bS`),
  `s_c = ⌈e^{n^.01}⌉` (`sC`), `η = 10^{-8}` (`etaC`) (11:12–36, 11:109);
* the inner coordinates `j < hIn n` and the outer coordinates `j ≥ hIn n` of `Q_n`; outer words index the slices;
* the slice experiment of one tag (11:35–64), written on the data it reads: the hit-conditioned law `ρ_y`
  (`rhoLaw`), the likelihood `L_b`, the normalizers `Z_b`, `Z_{b,-v}`, the gates and the posterior odd row
  `p_b^W` (`oddRowW`) as functions of the `h` neighbouring tuples, indexed by an inner direction;
* the first-side common-neighbour row `σ_v` (`sigmaW`, 11:67–70) as a function of the `h` internal odd outputs,
  and the radius-two data of an even role (`ballStar`: the centre tuple and one tuple per pair of inner
  directions);
* the mean rows `π_i = E_W p_b^W` (`meanOddRow`) and `α_i = E σ_v` (`meanEvenRow`) (11:95–100);
* the finite menu of P11.1-menu (`Menu11`, 11:26–33) and the compatibility predicates of Lemma 11.2
  (11:104–115);
* the interactions `M_J`, the envelope `w`, the alternating sum `Φ_u` and the outer mass `Z` of Lemma 11.3
  (11:167–331).
-/

namespace HypercubeRamsey.S11.Core

open HypercubeRamsey OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

/-! ## Parameters (11:12–36, 11:109) -/

/-- The inner slice dimension `h = ⌊n^.1⌋`. -/
def hIn (n : ℕ) : ℕ := Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 10))

/-- The tuple length `k = ⌈n^.2⌉`. -/
def kTup (n : ℕ) : ℕ := Nat.ceil ((n : ℝ) ^ ((1 : ℝ) / 5))

/-- The surplus `g = n^{-.01}`. -/
def gS (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 100)

/-- The discrepancy error `b_* = n^{-1+.05}` of (11.1). -/
def bS (n : ℕ) : ℝ := (n : ℝ) ^ (-(19 : ℝ) / 20)

/-- The clique size `s_c = ⌈e^{n^ζ}⌉`, `ζ = 1/100`. -/
def sC (n : ℕ) : ℕ := Nat.ceil (Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100)))

/-- The high-degree tolerance `η = 10^{-8}` of Lemma 11.2. -/
def etaC : ℝ := 1 / 100000000

/-! ## Cube coordinates and roles -/

/-- Inner coordinates of `Q_n`: the first `hIn n` coordinates. -/
abbrev InnerCoord (n : ℕ) := {j : Fin n // j.val < hIn n}

/-- Outer coordinates of `Q_n`. -/
abbrev OuterCoord (n : ℕ) := {j : Fin n // hIn n ≤ j.val}

/-- Outer words; each indexes one inner slice. -/
abbrev OuterWord (n : ℕ) := OuterCoord n → Bool

/-- Even roles (first side). -/
abbrev EvenRole (n : ℕ) := {v : CubeVertex n // IsEvenRole v}

/-- Odd roles (second side). -/
abbrev OddRole (n : ℕ) := {v : CubeVertex n // ¬ IsEvenRole v}

/-- The odd neighbour of an even role across coordinate `j`. -/
def oddNbr {n : ℕ} (a : EvenRole n) (j : Fin n) : OddRole n :=
  ⟨cubeFlip a.1 j, fun h => ((cubeFlip_parity a.1 j).mp h) a.2⟩

/-- The even neighbour of an odd role across coordinate `j`. -/
def evenNbr {n : ℕ} (b : OddRole n) (j : Fin n) : EvenRole n :=
  ⟨cubeFlip b.1 j, (cubeFlip_parity b.1 j).mpr b.2⟩

/-- The slice (outer word) of a vertex. -/
def sliceOf {n : ℕ} (v : CubeVertex n) : OuterWord n := fun j => v j.1

/-- Flip one outer coordinate of an outer word. -/
def flipOuter {n : ℕ} (s : OuterWord n) (j : OuterCoord n) : OuterWord n :=
  Function.update s j (!s j)

/-- Hamming distance of outer words. -/
def wordDist {n : ℕ} (s s' : OuterWord n) : ℕ :=
  (Finset.univ.filter fun j => s j ≠ s' j).card

/-- Outer-word balls. -/
def wordBall {n : ℕ} (s : OuterWord n) (r : ℕ) : Finset (OuterWord n) :=
  Finset.univ.filter fun s' => wordDist s s' ≤ r

/-- Full-cube balls of even roles. -/
def evenBall {n : ℕ} (v : EvenRole n) (r : ℕ) : Finset (EvenRole n) :=
  Finset.univ.filter fun v' => HypercubeRamsey.hammingDist v.1 v'.1 ≤ r

/-! ## The slice experiment of one tag (11:35–64) -/

/-- Unordered pairs of inner directions; `v + e_a + e_c` is the even role at inner distance two indexed by
`{a, c}`. -/
abbrev Pair (I : Type) [Fintype I] [DecidableEq I] := {S : Finset I // S.card = 2}

section Slice

variable {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)

/-- The hit-conditioned first law `ρ_y(w) = μ(w) 1[w ∼_G y] / d_G(μ, y)` (11:37–39); the law `μ` itself when
`d_G(μ, y) = 0` (never used: base labels have degree at least `1/2`). -/
def rhoLaw (μ : Law N) (y : Fin N) : Law N :=
  if h : 0 < colDeg E G μ y then
    { w := fun x => μ.w x * hit E G x y / colDeg E G μ y
      nonneg := fun x => div_nonneg (mul_nonneg (μ.nonneg x) (by unfold hit; split_ifs <;> norm_num)) h.le
      sum_eq_one := by rw [← Finset.sum_div]; exact div_self h.ne' }
  else μ

/-- The law `ρ_y^{⊗k}` of one tuple. -/
def tupLaw (μ : Law N) (y : Fin N) (k : ℕ) : FinProb (Fin k → Fin N) :=
  FinProb.pi fun _ : Fin k => rhoLaw E G μ y

/-- The weight of one tuple under `ρ_y^{⊗k}`. -/
def tupW {k : ℕ} (μ : Law N) (y : Fin N) (t : Fin k → Fin N) : ℝ :=
  ∏ j, (rhoLaw E G μ y).w (t j)

variable {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}

/-- The weight of `h` independent tuples (one per inner direction) under `ρ_y^{⊗k}`. -/
def starW (μ : Law N) (y : Fin N) (ws : I → Fin k → Fin N) : ℝ :=
  ∏ a, tupW E G μ y (ws a)

/-- The likelihood `L_b(y) = ∏_w 1[w ∼_G y] / d_G(μ, y)` of the tuples at the internal even neighbours of an odd
role (11:40–44). -/
def lik (μ : Law N) (ws : I → Fin k → Fin N) (y : Fin N) : ℝ :=
  ∏ a, ∏ j, hit E G (ws a j) y / colDeg E G μ y

/-- The likelihood with the tuple of direction `a₀` omitted. -/
def likDel (μ : Law N) (ws : I → Fin k → Fin N) (a₀ : I) (y : Fin N) : ℝ :=
  ∏ a ∈ Finset.univ.erase a₀, ∏ j, hit E G (ws a j) y / colDeg E G μ y

/-- `Z_b = ∫ L_b dν` (11:45). -/
def normZ (μ ν : Law N) (ws : I → Fin k → Fin N) : ℝ := ∑ y, ν.w y * lik E G μ ws y

/-- `Z_{b,-v}` (11:45). -/
def normZDel (μ ν : Law N) (ws : I → Fin k → Fin N) (a₀ : I) : ℝ :=
  ∑ y, ν.w y * likDel E G μ ws a₀ y

/-- The gates of an odd row (11:45–49): positivity, `Z_b ≥ e^{-kh}`, and `Z_b / Z_{b,-v} ≥ e^{-.2gk}` for every
internal neighbour (in multiplicative form). -/
def Passes (g : ℝ) (μ ν : Law N) (ws : I → Fin k → Fin N) : Prop :=
  0 < normZ E G μ ν ws ∧ Real.exp (-((k : ℝ) * Fintype.card I)) ≤ normZ E G μ ν ws ∧
    ∀ a, Real.exp (-(1 / 5 : ℝ) * g * k) * normZDel E G μ ν ws a ≤ normZ E G μ ν ws

/-- The odd row `p_b^W` (11:50): `ν L_b / Z_b` on passing, `ν` otherwise. -/
def oddRowW (g : ℝ) (μ ν : Law N) (ws : I → Fin k → Fin N) (y : Fin N) : ℝ :=
  if Passes E G g μ ν ws then ν.w y * lik E G μ ws y / normZ E G μ ν ws else ν.w y

/-- The first-side common-neighbour set of the internal odd outputs `z` inside `supp μ` (11:68). -/
def commonSet (μ : Law N) (z : I → Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun x => μ.w x ≠ 0 ∧ ∀ a, Hits E G x (z a)

/-- The row `σ_v` (11:67–70): uniform on the common-neighbour set when it has at least
`N exp(-(log 2 - g/2) h)` labels, zero otherwise. -/
def sigmaW (g : ℝ) (μ : Law N) (z : I → Fin N) (x : Fin N) : ℝ :=
  if x ∈ commonSet E G μ z ∧
      (N : ℝ) * Real.exp (-((Real.log 2 - g / 2) * Fintype.card I)) ≤ ((commonSet E G μ z).card : ℝ)
  then ((commonSet E G μ z).card : ℝ)⁻¹ else 0

/-- The neighbouring tuples of the internal odd neighbour `v + e_a` of an even role `v`, read from the radius-two
data `W` (`none` is `v` itself; `some {a, c}` is `v + e_a + e_c`). -/
def ballStar (W : Option (Pair I) → Fin k → Fin N) (a : I) : I → Fin k → Fin N :=
  fun c => if hc : c = a then W none else W (some ⟨{a, c}, Finset.card_pair (Ne.symm hc)⟩)

/-- The weight of the radius-two data under independent `ρ_{y₀}^{⊗k}` tuples. -/
def ballW (μ : Law N) (y₀ : Fin N) (W : Option (Pair I) → Fin k → Fin N) : ℝ :=
  ∏ o, tupW E G μ y₀ (W o)

/-- The weight of the internal odd outputs `z` given the radius-two data: independent draws from the odd rows. -/
def outW (g : ℝ) (μ ν : Law N) (W : Option (Pair I) → Fin k → Fin N) (z : I → Fin N) : ℝ :=
  ∏ a, oddRowW E G g μ ν (ballStar W a) (z a)

end Slice

section SliceMeans

variable {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
variable (I : Type) [Fintype I] [DecidableEq I] (k : ℕ)

/-- The test-failure probability of one odd row at a fixed base label `y₀` (11:52–56, 11:65). -/
def testFail (g : ℝ) (μ ν : Law N) (y₀ : Fin N) : ℝ :=
  ∑ ws : I → Fin k → Fin N, starW E G μ y₀ ws * (if Passes E G g μ ν ws then 0 else 1)

/-- The mean odd row `π_i = E_W p_b^W` (11:97). -/
def meanOddRow (g : ℝ) (μ ν : Law N) (y₀ y : Fin N) : ℝ :=
  ∑ ws : I → Fin k → Fin N, starW E G μ y₀ ws * oddRowW E G g μ ν ws y

/-- The mean even subprobability row `α_i = E_{W, Y_{N_in(v)} | W} σ_v` (11:98). -/
def meanEvenRow (g : ℝ) (μ ν : Law N) (y₀ x : Fin N) : ℝ :=
  ∑ W : Option (Pair I) → Fin k → Fin N, ballW E G μ y₀ W *
    ∑ z : I → Fin N, outW E G g μ ν W z * sigmaW E G g μ z x

/-- The probability that `σ_v` does not have mass one in the slice reference law (11:70). -/
def sigmaFail (g : ℝ) (μ ν : Law N) (y₀ : Fin N) : ℝ :=
  ∑ W : Option (Pair I) → Fin k → Fin N, ballW E G μ y₀ W *
    ∑ z : I → Fin N, outW E G g μ ν W z * (if ∑ x, sigmaW E G g μ z x = 1 then 0 else 1)

end SliceMeans

/-! ## The menu (11:26–33) -/

/-- A finite one-colour menu of biased patches (11:26–33): supports in the retained sets, `width μ_i ≤ n^.01`,
`width ν_i ≤ .011 n`, all columns of `ν_i` of degree at least `1/2 + 2g`, and every removal pair of at most `κN`
labels per side avoided by the supports of some tag. -/
structure Menu11 (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (κ : ℝ) where
  ι : Type
  [fin : Fintype ι]
  G : Colour
  μ : ι → Law N
  ν : ι → Law N
  μ_supp : ∀ i, (μ i).SupportedIn X
  ν_supp : ∀ i, (ν i).SupportedIn Y
  μ_width : ∀ i, (μ i).WidthLE ((n : ℝ) ^ ((1 : ℝ) / 100))
  ν_width : ∀ i, (ν i).WidthLE ((11 / 1000 : ℝ) * n)
  high : ∀ i y, (ν i).w y ≠ 0 → 1 / 2 + 2 * gS n ≤ colDeg E G (μ i) y
  avail : ∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N → (RY.card : ℝ) ≤ κ * N →
    ∃ i, (∀ x ∈ RX, (μ i).w x = 0) ∧ (∀ y ∈ RY, (ν i).w y = 0)

attribute [instance] Menu11.fin

/-- Profile mixture of a family of weight functions. -/
def mixW {ι : Type} [Fintype ι] {N : ℕ} (p : FinProb ι) (f : ι → Fin N → ℝ) (x : Fin N) : ℝ :=
  ∑ i, p.w i * f i x

section MenuRows

variable {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}

/-- The mean odd row `π_i` of tag `i` at its base label. -/
def piRow (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (i : M.ι) (y : Fin N) : ℝ :=
  meanOddRow E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i) y

/-- The mean even row `α_i` of tag `i` at its base label. -/
def alphaRow (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (i : M.ι) (x : Fin N) : ℝ :=
  meanEvenRow E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i) x

/-- `π = ∑ p_i π_i`. -/
def piBar (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) : Fin N → ℝ :=
  mixW p (piRow M y₀)

/-- `∑ p_i α_i`. -/
def alphaBar (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) : Fin N → ℝ :=
  mixW p (alphaRow M y₀)

end MenuRows

/-! ## Compatibility (11:104–115) -/

section Compat

variable {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)

/-- `m_x = E_π f_x`. -/
def sMean (π : Fin N → ℝ) (x : Fin N) : ℝ := ∑ y, π y * fv E G x y

/-- No `s_c` pairwise-distinct labels of `S` with all mutual `K_π > 8 n^{-δ}`. -/
def NoClique (π : Fin N → ℝ) (n : ℕ) (δ : ℝ) (S : Finset (Fin N)) : Prop :=
  ∀ C : Finset (Fin N), C ⊆ S → C.card = sC n →
    ∃ x ∈ C, ∃ z ∈ C, x ≠ z ∧ corr E G π x z ≤ 8 * (n : ℝ) ^ (-δ)

/-- Lemma 11.2's compatibility of the tag `i` with the profile `p` (11:110–114). -/
def CompatTag (n : ℕ) (δ : ℝ) {ι : Type} [Fintype ι] (μ : ι → Law N) (π : ι → Fin N → ℝ)
    (p : FinProb ι) (i : ι) : Prop :=
  (∀ x, (μ i).w x ≠ 0 → |sMean E G (mixW p π) x| ≤ 4 * bS n) ∧
  (∀ x, (μ i).w x ≠ 0 →
    (∑ i' ∈ Finset.univ.filter (fun i' => (4 / 5 : ℝ) < deg E G (π i') x), p.w i') ≤ etaC) ∧
  NoClique E G (mixW p π) n δ (Finset.univ.filter fun x => (μ i).w x ≠ 0)

end Compat

/-- The balance (11.2) with constant `K`. -/
def Balanced {N : ℕ} {ι : Type} [Fintype ι] (K : ℝ) (p : FinProb ι) (π α : ι → Fin N → ℝ) : Prop :=
  (∀ y, (N : ℝ) * mixW p π y ≤ K) ∧ (∀ x, (N : ℝ) * mixW p α x ≤ K)

/-- The inputs of Lemma 11.2: a menu at tolerance `κ` with odd mean rows `π_i` (laws on `supp ν_i`, width
`.02n`) and even mean rows `α_i` (subprobabilities on `supp μ_i`). -/
structure ProfileInput (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (κ : ℝ) {ι : Type}
    [Fintype ι] (μ ν : ι → Law N) (π α : ι → Fin N → ℝ) : Prop where
  host : 2 ^ n ≤ N
  μ_supp : ∀ i, (μ i).SupportedIn X
  ν_supp : ∀ i, (ν i).SupportedIn Y
  avail : ∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N → (RY.card : ℝ) ≤ κ * N →
    ∃ i, (∀ x ∈ RX, (μ i).w x = 0) ∧ (∀ y ∈ RY, (ν i).w y = 0)
  π_nonneg : ∀ i y, 0 ≤ π i y
  π_sum : ∀ i, ∑ y, π i y = 1
  π_supp : ∀ i y, π i y ≠ 0 → (ν i).w y ≠ 0
  π_cap : ∀ i y, (N : ℝ) * π i y ≤ Real.exp ((n : ℝ) / 50)
  α_nonneg : ∀ i x, 0 ≤ α i x
  α_sum : ∀ i, ∑ x, α i x ≤ 1
  α_supp : ∀ i x, α i x ≠ 0 → (μ i).w x ≠ 0

/-- Cluster absence on `(X, Y)` (Corollary 10.2 at one dimension, `ζ = 1/100`). -/
def ClusterAbsXY (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (δ : ℝ) : Prop :=
  ∀ (G : Colour) A B, A ⊆ X → B ⊆ Y → (A, B) ∉ PCluster G ((1 / 100 : ℚ) : ℝ) δ n N E

/-- Cluster absence in the reversed orientation `(Y, X)`. -/
def ClusterAbsYX (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (δ : ℝ) : Prop :=
  ∀ (G : Colour) A B, A ⊆ Y → B ⊆ X → (A, B) ∉ PCluster G ((1 / 100 : ℚ) : ℝ) δ n N (transposeRel E)

/-! ## The outer moment (11:167–331) -/

/-- The product weight `σ^{⊗u}` of a tuple. -/
def tupWt {N : ℕ} (σ : Fin N → ℝ) {u : ℕ} (x : Fin u → Fin N) : ℝ := ∏ j, σ (x j)

/-- The product weight `π^{⊗D}` of an outer word of labels. -/
def outWt {N : ℕ} (π : Fin N → ℝ) {D : Type} [Fintype D] (Yv : D → Fin N) : ℝ := ∏ l, π (Yv l)

section Outer

variable {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)

/-- `a_x(y) = 1[x ∼_G y] / D_x - 1` with `D_x = d_G(x; π)` (11:172–175). -/
def aF (π : Fin N → ℝ) (x y : Fin N) : ℝ := hit E G x y / deg E G π x - 1

/-- The interaction `M_J = ∫ ∏_{j ∈ J} a_{x_j} dπ` of a tuple (11:190–193). -/
def inter (π : Fin N → ℝ) {u : ℕ} (J : Finset (Fin u)) (x : Fin u → Fin N) : ℝ :=
  ∑ y, π y * ∏ j ∈ J, aF E G π (x j) y

/-- The envelope `w = max_{|J| ≥ 2} |M_J|`, zero for an empty maximum (11:283). -/
def env (π : Fin N → ℝ) {u : ℕ} (x : Fin u → Fin N) : ℝ :=
  (Finset.univ : Finset (Finset (Fin u))).sup' ⟨∅, Finset.mem_univ _⟩ fun J =>
    if 2 ≤ J.card then |inter E G π J x| else 0

/-- The alternating sum `Φ_u` with exponent `d` (11:295–300). -/
def phiU (π : Fin N → ℝ) (d u : ℕ) (x : Fin u → Fin N) : ℝ :=
  ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) * (∑ y, π y * ∏ j ∈ I, (1 + aF E G π (x j) y)) ^ d

/-- The outer mass `Z = ∫ ∏_l (1 + a_x(Y_l)) dσ(x)` of the outer labels `Yv` (11:178, 187). -/
def outerZ (π σ : Fin N → ℝ) {D : Type} [Fintype D] (Yv : D → Fin N) : ℝ :=
  ∑ x, σ x * ∏ l, (1 + aF E G π x (Yv l))

/-- The failure probability `Pr{Z < 1/2}` under independent outer labels `Y_l ∼ π` (11:177–181). -/
def outerFail (π σ : Fin N → ℝ) (D : Type) [Fintype D] [DecidableEq D] : ℝ :=
  ∑ Yv : D → Fin N, outWt π Yv * (if outerZ E G π σ Yv < 1 / 2 then 1 else 0)

end Outer

end

end HypercubeRamsey.S11.Core
