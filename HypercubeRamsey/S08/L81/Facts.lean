import HypercubeRamsey.S08.L81.Experiment

/-!
# Lemma 8.1: named step conclusions

Each node of L8.1 concludes one of these facts about a context `D`; a node that needs another node's conclusion
takes it as a hypothesis, and the assemblies supply it.  Source references are those of the node that proves the
fact.
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

namespace Ctx

variable {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)

/-! ## Steps 2 and 4 -/

/-- L8.1c: the raw probability that a base gate fails at a key is at most `e^{-n^{c'}}` (08:76–123). -/
def GateTail (c' : ℝ) : Prop :=
  ∀ g : D.KeyT, D.rawHidden.pr (fun Θ => ¬ D.BaseGates Θ g) ≤ Real.exp (-(D.n : ℝ) ^ c')

/-- L8.1e(i): on the candidate's gates the internal density of `S_g` against its reference is at most
`e^{hn^β + n^{τ/2} + 1}`, and a cross pair density at most `2^{h+2}` (08:144–154). -/
def DensityBounds : Prop :=
  ∀ (Θ : D.Hist) (g : D.KeyT) (ξ : D.Tup), D.CandGate (Function.update Θ g ξ) g →
    (∀ i, (D.tilt (Function.update Θ g ξ) g).w i ≤
      Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2) + 1) * (D.refInt Θ g).w i) ∧
    ∀ (u : D.CrossSub g) (q : D.M.ι × Fin D.N),
      (D.tilt (Function.update Θ g ξ) u.1).w q.1 * (D.anchorU (Function.update Θ g ξ) u.1 q.1).w q.2 ≤
        (2 : ℝ) ^ (h + 2) * (D.refCross Θ g u.1).w q

/-- L8.1e(ii): the denominator tail, `E_{ξ ∼ R'} q_{g,k}(Θ[g ↦ ξ]) ≤ ε₀` (08:162–163, 179–180). -/
def DenTail : Prop :=
  ∀ (Θ : D.Hist) (g : D.KeyT) (k : ℕ), D.R'.expect (fun ξ => D.qgk (Function.update Θ g ξ) g k) ≤ D.eps0

/-- L8.1e(iii): on `M ≥ ε₀`, a presentation with at most `T` internal tags has base posterior of `N^h`-density at
most `e^{1.5δhs log n}` (08:163–169). -/
def PostCap : Prop :=
  ∀ (Θ : D.Hist) (g : D.KeyT) (o : D.Obs D.Loc g),
    (Finset.univ.filter fun ℓ => (o.1 ℓ).isSome).card ≤ TC η₀ D.n → D.eps0 ≤ D.Mden Θ g o →
      ∀ ξ, (D.N : ℝ) ^ h * (D.basePost Θ g o).w ξ ≤
        Real.exp ((15 / 100000 : ℝ) * h * sC η₀ D.n * Real.log D.n)

/-- L8.1e(iv): every candidate with positive likelihood hits all observed cross anchors coordinatewise, and every
observed internal tag passes the cutoffs at `g` under that candidate (08:171–176). -/
def FSupport : Prop :=
  ∀ {J : Type} [Fintype J] (Θ : D.Hist) (g : D.KeyT) (ξ : D.Tup) (o : D.Obs J g), D.Fcand Θ g ξ o ≠ 0 →
    (∀ u, D.hitsAll (o.2 u).2 ξ) ∧ ∀ j i, o.1 j = some i → D.GateOpen (Function.update Θ g ξ) g i

/-! ## Step 5 -/

/-- L8.1f(ii): the hidden events satisfy the local-lemma input with scopes `B_grid(g, 2)`, charge `x` and degree
`(2s+1)^4` (08:184–189). -/
def HiddenLLL (x : ℝ) : Prop :=
  LLLInput (fun _ : D.KeyT => D.R') (fun g Θ => D.HBad Θ g) (fun g => keyBall g 2) x
    ((2 * sC η₀ D.n + 1) ^ 4)

/-- L8.1f(iii): on prospective ball counts at most `2λ`, an odd cell has at most `L_n = exp(25(s+T) log n)`
candidate lists (08:196–199). -/
def ListCount : Prop :=
  ∀ (P : D.Pos) (c : D.CellT), D.PosCountOK P c →
    ((Finset.univ.filter fun L : D.LList c.1 => D.Cand P c L).card : ℝ) ≤
      Real.exp (25 * (sC η₀ D.n + TC η₀ D.n : ℝ) * Real.log D.n)

/-- L8.1f(viii): at a hidden history avoiding the hidden events, a candidate list is bad with tag probability at
most `ε₀^{1/4}` (08:191–195). -/
def BadListProb : Prop :=
  ∀ Θ : D.Hist, (∀ g, ¬ D.HBad Θ g) → ∀ (P : D.Pos) (c : D.CellT) (L : D.LList c.1), D.Cand P c L →
    (D.tagLawAll Θ).pr (fun t => D.BadList Θ t c L) ≤ Real.sqrt (Real.sqrt D.eps0)

/-- L8.1f(iv): ball counts in `[λ/2, 2λ]` and fewer than `n` family lists give legal eligibility (`≥ λ/3`)
everywhere, since at most `O(n(n+s)(s+T)) = o(λ)` IDs are forbidden per site-level (08:208–212). -/
def LegalOfCounts : Prop :=
  ∀ (Θ : D.Hist) (P : D.Pos) (t : D.Tags), D.PosOK P → D.FewBad Θ P t →
    ∀ g b j, (hdP η₀ D.n).LegalAt (P g) (D.elig Θ P t g) b j

/-- L8.1f(v): on selection success every selection succeeds, internal fans have at most `T` IDs, the position gate
holds, every used list passes `q_L ≤ ε₀^{1/4}`, and eligibility is legal on every consultation domain
(08:130–131, 212–214). -/
def SelConseq : Prop :=
  ∀ q : D.Pre, D.SelOK q →
    (∀ e, (D.sel q e).isSome) ∧
    ∀ c : D.CellT, (D.intIds q c).card ≤ TC η₀ D.n ∧ D.PosCountOK q.1.2 c ∧
      D.qL q.1.1 c.1 (fun ℓ => if ℓ ∈ D.intIds q c then some (q.2.1.1 c.1 ℓ) else none)
        (fun u => q.2.1.1 u.1 (D.crossId q c u)) ≤ Real.sqrt (Real.sqrt D.eps0) ∧
      D.LocalLegal q.1.1 q.1.2 q.2.1.1 c

/-- L8.1f(vi): selection at `(t, b)` reads positions and tags only at keys in `B_grid(t, 2)` and locations in
`B_Q(b, r + 4H + 2)`, activations and ties only in slice `t` at those locations, and hidden tuples only in
`B_grid(t, 3)` (08:216–225). -/
def SelLocal : Prop :=
  ∀ (q q' : D.Pre) (e : D.CellT), (∀ g ∈ keyBall e.1 3, q.1.1 g = q'.1.1 g) →
    (∀ g ∈ keyBall e.1 2, ∀ ℓ : D.Loc, _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 →
      q.1.2 g ℓ = q'.1.2 g ℓ ∧ q.2.1.1 g ℓ = q'.2.1.1 g ℓ) →
    (∀ ℓ : D.Loc, _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 →
      q.2.1.2 e.1 ℓ = q'.2.1.2 e.1 ℓ ∧ q.2.2 e.1 ℓ = q'.2.2 e.1 ℓ) →
    D.sel q e = D.sel q' e

/-! ## Steps 6–8 -/

/-- L8.1g(i): the valid-presentation subdensity is dominated by the unselected product density,
`F_ξ a_ξ ≤ F_ξ` (08:230–234). -/
def GselLeF : Prop :=
  ∀ (Θ : D.Hist) (P : D.Pos) (c : D.CellT) (ξ : D.Tup) (π : D.Pres c.1),
    D.Gsel Θ P c ξ π ≤ D.Fcand Θ c.1 ξ (D.obsOf π)

/-- L8.1g(ii): on a valid presentation the selected posterior has `N^h`-density at most `e^{.003hs log n}`
(08:245–254). -/
def SelPostCap : Prop :=
  ∀ (q : D.Pre) (W : D.Anch) (c : D.CellT), D.PresValid q W c →
    ∀ ξ, (D.N : ℝ) ^ h * (D.selPost q.1.1 q.1.2 c (D.presOf q W c)).w ξ ≤
      Real.exp ((3 / 1000 : ℝ) * h * sC η₀ D.n * Real.log D.n)

/-- L8.1g(iii): `p⁰` is nonnegative; on valid presentations it is a probability law, at most `5/2` times the average
coordinate marginal of the selected posterior (the light mass is at least `.4`), with
`N max p⁰ ≤ 3 e^{.01 s log n}` (08:256–264). -/
def P0Law : Prop :=
  ∀ (q : D.Pre) (W : D.Anch) (c : D.CellT), (∀ y, 0 ≤ D.p0 q W c y) ∧
    (D.PresValid q W c → ∑ y, D.p0 q W c y = 1 ∧
      (∀ y, D.p0 q W c y ≤
        (5 / 2 : ℝ) * averageCoordinateMarginal (D.selPost q.1.1 q.1.2 c (D.presOf q W c)) y) ∧
      ∀ y, (D.N : ℝ) * D.p0 q W c y ≤ 3 * Real.exp D.heavyB)

/-- L8.1g(iv): `p⁰` is supported on labels hitting every cross anchor (08:293). -/
def P0Support : Prop :=
  ∀ (q : D.Pre) (W : D.Anch) (c : D.CellT) (y : Fin D.N), D.p0 q W c y ≠ 0 →
    ∀ u ∈ crossKeys c.1, Hits D.E D.G (W (u, c.2)) y

/-- L8.1g(v): the raw mean bound `E p⁰_{g,a}(y) ≤ 16K/N` in the experiment of Step 6: target tuple from `R'`, raw
tags, selections and anchors, at fixed positions and non-target tuples (08:266–283). -/
def P0RawMean (K : ℝ) : Prop :=
  ∀ (Θ : D.Hist) (P : D.Pos) (c : D.CellT) (y : Fin D.N),
    ∑ ξ, D.R'.w ξ * (D.rawLaw (Function.update Θ c.1 ξ) P).expect
      (fun z => D.p0 ((Function.update Θ c.1 ξ, P), z.1) z.2 c y) ≤ 16 * K / D.N

/-- L8.1g(vi): `p⁰` at `(g, a)` reads hidden tuples in `B_grid(g, 4)`, positions and tags in `B_grid(g, 3)`,
activations and ties in `B_grid(g, 1)`, and only the cross anchors `W_{u,a}` (08:285–290). -/
def P0Local : Prop :=
  ∀ (q q' : D.Pre) (W W' : D.Anch) (c : D.CellT),
    (∀ g ∈ keyBall c.1 4, q.1.1 g = q'.1.1 g) →
    (∀ g ∈ keyBall c.1 3, q.1.2 g = q'.1.2 g ∧ q.2.1.1 g = q'.2.1.1 g) →
    (∀ g ∈ keyBall c.1 1, q.2.1.2 g = q'.2.1.2 g ∧ q.2.2 g = q'.2.2 g) →
    (∀ u ∈ crossKeys c.1, W (u, c.2) = W' (u, c.2)) →
    D.p0 q W c = D.p0 q' W' c

/-- The ordinary even cells of the odd cell `c`. -/
def ordCells (c : D.CellT) : Finset D.CellT := (ordNbrs c.2).image fun b => (c.1, b)

/-- L8.1h(i): with tags in the support of their laws and a valid presentation, the ordinary-hit test fails with
probability at most `50(n+1)Δ/(1-Δ)` over independent raw ordinary anchors (08:295–297). -/
def HitTail : Prop :=
  ∀ (q : D.Pre) (W : D.Anch) (c : D.CellT), D.Supp q → D.PresValid q W c →
    ∑ a : (∀ e : D.ordCells c, Fin D.N), (∏ e : D.ordCells c, (D.Usel q e.1).w (a e)) *
      (if D.HitFail q (glue (D.ordCells c) W a) c then 1 else 0) ≤
        50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ)

/-- L8.1h(ii): odd rows are nonnegative, supported on labels hitting every padded even anchor, and on validity
probability laws with `p ≤ p⁰/.98` and `N max p ≤ e^{.02 s log n}` (08:293–300). -/
def PRowFacts : Prop :=
  ∀ (q : D.Pre) (W : D.Anch) (c : D.CellT),
    (∀ y, 0 ≤ D.prow q W c y) ∧
    (∀ y, D.prow q W c y ≠ 0 → ∀ e, PadNbr c e → Hits D.E D.G (W e) y) ∧
    (D.Valid8 q W c → ∑ y, D.prow q W c y = 1 ∧ (∀ y, D.prow q W c y ≤ D.p0 q W c y / (98 / 100)) ∧
      ∀ y, (D.N : ℝ) * D.prow q W c y ≤ Real.exp ((2 / 100 : ℝ) * sC η₀ D.n * Real.log D.n))

/-! ## Step 9 -/

/-- L8.1i(i): with hidden events avoided, the gated selected load at an even cell has raw mean (positions, tags,
activations, ties) at most `B_g(x)` (08:313–332). -/
def SelectMean : Prop :=
  ∀ Θ : D.Hist, (∀ g, ¬ D.HBad Θ g) → ∀ (e : D.CellT) (x : Fin D.N),
    D.posLaw.expect (fun P => (D.rawTAT Θ).expect (fun ω =>
      (if D.LocalLegal Θ P ω.1.1 e then 1 else 0) * D.selLoad ((Θ, P), ω) e x)) ≤ D.Bcomp Θ e.1 x

/-- L8.1i(ii): `E_raw B_g(x) ≤ 40K` (08:336–343). -/
def BcompMean (K : ℝ) : Prop := ∀ (g : D.KeyT) (x : Fin D.N), D.rawHidden.expect (fun Θ => D.Bcomp Θ g x) ≤ 40 * K

/-! ## Step 10 -/

/-- L8.1j(i): on a successful history the denominator test fails with raw probability at most `ε₀^{1/4}`
(08:366). -/
def DenFailProb : Prop :=
  ∀ q : D.Pre, D.Good q → ∀ c, (D.rawAnchors q).pr (fun W => D.DenFail q W c) ≤ Real.sqrt (Real.sqrt D.eps0)

/-- L8.1j(ii): on a successful history the hit test fails (with the denominator test passed) with raw probability
at most `50(n+1)Δ/(1-Δ)` (08:366). -/
def HitFailProb : Prop :=
  ∀ q : D.Pre, D.Good q → ∀ c,
    (D.rawAnchors q).pr (fun W => ¬ D.DenFail q W c ∧ D.HitFail q W c) ≤ 50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ)

/-- L8.1j(iii): `F_z ≤ e^{.03n} Q_v` (08:379–381). -/
def StarLikBound : Prop :=
  ∀ (q : D.Pre) (W : D.Anch) (v : CubeVertex D.n) (z : Fin D.N) (y : Fin D.n → Fin D.N),
    D.starLik q W v z y ≤ Real.exp ((3 / 100 : ℝ) * D.n) * D.starRef q W v y

/-- L8.1j(iv): `Q_v` does not read the anchor of `v`'s cell (08:377–378). -/
def StarRefUpdate : Prop :=
  ∀ (q : D.Pre) (W : D.Anch) (v : CubeVertex D.n) (z : Fin D.N),
    D.starRef q (Function.update W (cellOf η₀ v) z) v = D.starRef q W v

/-- L8.1j(v): the mean alarm rate over the anchor of the role's cell is at most `e^{-.04n}` (08:383–385). -/
def AlarmMean : Prop :=
  ∀ (q : D.Pre) (W : D.Anch) (a : EvenRole D.n),
    ∑ z, (D.Usel q (cellOf η₀ a.1)).w z * D.alarmRate q (Function.update W (cellOf η₀ a.1) z) a.1 ≤
      Real.exp (-(4 / 100 : ℝ) * D.n)

/-- L8.1j(vi): the alarm probability of a cell over its anchor, uniformly in the other anchors (08:385–389). -/
def AlarmProb : Prop :=
  ∀ (q : D.Pre) (W : D.Anch) (c : D.CellT),
    ∑ z, (D.Usel q c).w z * (if D.Alarm q (Function.update W c z) c then 1 else 0) ≤
      ((D.n : ℝ) + 1) ^ (2 * sC η₀ D.n + 1) * Real.exp (-(2 / 100 : ℝ) * D.n)

/-- L8.1j(vii): the event of a cell reads the anchors in its radius-two cell ball (08:387). -/
def CellBadScope : Prop :=
  ∀ (q : D.Pre) (c : D.CellT), FinProb.DependsOn (fun W : D.Anch => D.CellBad q W c) (cellBall c 2)

/-- The local-lemma input for the cell events at a fixed history (08:387–393): independent anchors, scopes the
radius-two balls, degree `(2s + (n - m) + 1)^4`. -/
def AnchorLLL (q : D.Pre) (x : ℝ) : Prop :=
  LLLInput (fun c : D.CellT => D.Usel q c) (fun c W => D.CellBad q W c) (fun c => cellBall c 2) x
    ((2 * sC η₀ D.n + dC η₀ D.n + 1) ^ 4)

/-! ## Steps 11–12 -/

/-- L8.1k(i): joint moments of grid-separated odd rows on success (08:396–413). -/
def OddMoment (C : ℝ) : Prop :=
  ∀ (y : Fin D.N) (l : ℕ), l ≤ D.n → ∀ u : Fin l → OddRole D.n,
    (∀ i j, i ≠ j → 8 < keyDist (keyOf η₀ (u i).1) (keyOf η₀ (u j).1)) →
    D.stagedLaw.expect (fun z => (if D.Good z.1 then 1 else 0) *
      ∏ i, (D.N : ℝ) * D.prow z.1 z.2 (cellOf η₀ (u i).1) y) ≤ C ^ l

/-- L8.1l(i): on predictive success the posterior even row is a probability law on the common neighbours of the
odd labels (08:431–432). -/
def EvenRowLaw : Prop :=
  ∀ (q : D.Pre) (W : D.Anch) (f : OddRole D.n → Fin D.N) (a : EvenRole D.n),
    ¬ D.PredFail q W a.1 (nbrLabels f a) →
    (∀ x, 0 ≤ D.evenRow q W f a x) ∧ (∑ x, D.evenRow q W f a x = 1) ∧
      ∀ x, D.evenRow q W f a x ≠ 0 → ∀ b : OddRole D.n, (cube D.n).Adj a.1 b.1 → Hits D.E D.G x (f b)

/-- L8.1l(ii): `N max w_v ≤ e^{.1n}` on success and predictive success (08:433–437). -/
def EvenRowCap : Prop :=
  ∀ (q : D.Pre) (W : D.Anch) (a : EvenRole D.n) (y : Fin D.n → Fin D.N), D.Good q →
    ¬ D.PredFail q W a.1 y → ∀ x, (D.N : ℝ) * D.evenRowAt q W a y x ≤ Real.exp ((1 / 10 : ℝ) * D.n)

/-- L8.1l(iii): the star cancellation at one role (08:441–449). -/
def StarCancel : Prop :=
  ∀ (q : D.Pre) (W : D.Anch) (a : EvenRole D.n) (x : Fin D.N),
    ∑ z, (D.Usel q (cellOf η₀ a.1)).w z * D.evenStar q (Function.update W (cellOf η₀ a.1) z) a x ≤
      (D.N : ℝ) * (D.Usel q (cellOf η₀ a.1)).w x

/-- L8.1l(iv): the clock comparison for residual-separated even roles at a successful prehistory (08:439). -/
def ClockFactor (q : D.Pre) (J : D.Anch → FinProb (OddRole D.n → Fin D.N)) : Prop :=
  ∀ W, D.GoodPre q W → ∀ (x : Fin D.N) (l : ℕ), l ≤ D.n → ∀ a : Fin l → EvenRole D.n,
    (∀ i j, i ≠ j → 4 < _root_.hammingDist (resOf η₀ (a i).1) (resOf η₀ (a j).1)) →
    ∑ f, (J W).w f * ∏ i, (D.N : ℝ) * D.evenRow q W f (a i) x ≤ 2 * ∏ i, D.evenStar q W (a i) x

/-- L8.1l(v): the anchor integral of separated star integrals (08:439–449). -/
def EvenAnchorIntegral (q : D.Pre) : Prop :=
  ∀ (x : Fin D.N) (l : ℕ), l ≤ D.n → ∀ a : Fin l → EvenRole D.n,
    (∀ i j, i ≠ j → 4 < _root_.hammingDist (resOf η₀ (a i).1) (resOf η₀ (a j).1)) →
    (D.anchorLaw q).expect (fun W => ∏ i, D.evenStar q W (a i) x) ≤
      2 ^ l * ∏ i, (D.N : ℝ) * (D.Usel q (cellOf η₀ (a i).1)).w x

/-- L8.1l(vi): separated even-role products under anchors and clock sampling (08:439–453). -/
def EvenMoment (q : D.Pre) (J : D.Anch → FinProb (OddRole D.n → Fin D.N)) : Prop :=
  ∀ (x : Fin D.N) (l : ℕ), l ≤ D.n → ∀ a : Fin l → EvenRole D.n,
    (∀ i j, i ≠ j → 4 < _root_.hammingDist (resOf η₀ (a i).1) (resOf η₀ (a j).1)) →
    ∑ W, (D.anchorLaw q).w W *
        (if D.GoodPre q W then ∑ f, (J W).w f * ∏ i, (D.N : ℝ) * D.evenRow q W f (a i) x else 0) ≤
      4 ^ l * ∏ i, (D.N : ℝ) * (D.Usel q (cellOf η₀ (a i).1)).w x

end Ctx

end HypercubeRamsey.S08
