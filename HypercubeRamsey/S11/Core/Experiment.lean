import HypercubeRamsey.S11.Core.Slice
import HypercubeRamsey.S11.Core.OuterMoment
import HypercubeRamsey.S07.Experiment

/-!
# Proposition 11.1: the assignment experiment on the full cube

Source: `sections/11-…tex`, lines 333–394.  The experiment is written directly on `Q_n` with its inner and outer
coordinates; the slice laws of `Slice.lean` and `Definitions.lean` enter through the data each object reads:

* tags `t : OuterWord n → ι`, raw law `p^{⊗}` (`rawTags`, 11:337);
* tuples `W : EvenRole n → Fin k → Fin N`, raw law `∏_v ρ_{y₀(t(s(v)))}^{⊗k}` (`rawTuples`, 11:337, 371);
* odd rows `p_b^W` read the tuples at the internal even neighbours of `b` (`oddRowF`); odd outputs are drawn
  independently from them (`oddProdW`);
* the unnormalized even row `M_v(x) = σ_v(x) ∏_{j outer} 1[x ∼_G Y_{v^j}] / D_x` (`evenRowF`, 11:338–342) and
  its mass failure;
* the tag events `T1`, `T2` and the tag law (11:344–354), the comparison means `A_s`, `B_s` and typical tags
  (11:356–368);
* the tuple events and the tuple law (11:370–371), odd column sums (11:373–375), the clock output (11:377–378);
* the named facts of the stage nodes (moments and the star mean, 11:373–390).
-/

namespace HypercubeRamsey.S11.Core

open HypercubeRamsey OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

/-- Everything fixed before the assignment (11:333–335): host bounds, the slice facts, a balanced compatible
profile (Lemma 11.2 with constant `K`), and (11.1). -/
structure Fixed11 (δ x₀ K : ℝ) (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (κ : ℝ)
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) : Prop where
  host : 2 ^ n ≤ N
  hostUp : N ≤ n * 2 ^ n
  slice : SliceFacts M y₀
  balanced : Balanced K p (piRow M y₀) (alphaRow M y₀)
  compat : ∀ i, p.w i ≠ 0 → CompatTag E M.G n δ M.μ (piRow M y₀) p i
  disc : DiscOne E X Y ((n : ℝ) ^ ((1 : ℝ) - δ / 16)) ((n : ℝ) ^ x₀) ((n : ℝ) ^ (-(19 : ℝ) / 20))

/-! ## Raw laws, rows and mass failure (11:336–342) -/

variable {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}

/-- Independent tags `i(s) ∼ p` at the outer words. -/
def rawTags (M : Menu11 n N E X Y κ) (p : FinProb M.ι) : FinProb (OuterWord n → M.ι) :=
  FinProb.pi fun _ : OuterWord n => p

/-- Raw tuples given the tags: independent `W_v ∼ ρ_{y₀(i(s(v)))}^{⊗k}`. -/
def rawTuples (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (t : OuterWord n → M.ι) :
    FinProb (EvenRole n → Fin (kTup n) → Fin N) :=
  FinProb.pi fun v : EvenRole n => tupLaw E M.G (M.μ (t (sliceOf v.1))) (y₀ (t (sliceOf v.1))) (kTup n)

/-- The tuples at the internal even neighbours of an odd role, indexed by the inner direction. -/
def starOf {k : ℕ} (W : EvenRole n → Fin k → Fin N) (b : OddRole n) : InnerCoord n → Fin k → Fin N :=
  fun a => W (evenNbr b a.1)

/-- The odd row `p_b^W` with the tag of `b`'s slice. -/
def oddRowF (M : Menu11 n N E X Y κ) (t : OuterWord n → M.ι) (W : EvenRole n → Fin (kTup n) → Fin N)
    (b : OddRole n) (y : Fin N) : ℝ :=
  oddRowW E M.G (gS n) (M.μ (t (sliceOf b.1))) (M.ν (t (sliceOf b.1))) (starOf W b) y

/-- The weight of an odd assignment under independent odd-row sampling given the tuples. -/
def oddProdW (M : Menu11 n N E X Y κ) (t : OuterWord n → M.ι) (W : EvenRole n → Fin (kTup n) → Fin N)
    (f : OddRole n → Fin N) : ℝ :=
  ∏ b, oddRowF M t W b (f b)

/-- The outputs at the internal odd neighbours of an even role. -/
def innerOut (f : OddRole n → Fin N) (v : EvenRole n) : InnerCoord n → Fin N :=
  fun a => f (oddNbr v a.1)

/-- The unnormalized even row `M_v(x) = σ_v(x) ∏_{j outer} 1[x ∼_G Y_{v^j}] / D_x`, `D_x = d_G(x; π)`
(11:338–341). -/
def evenRowF (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι)
    (f : OddRole n → Fin N) (v : EvenRole n) (x : Fin N) : ℝ :=
  sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x *
    ∏ j : OuterCoord n, hit E M.G x (f (oddNbr v j.1)) / deg E M.G (piBar M y₀ p) x

/-- Mass failure `‖M_v‖₁ < 1/2` at an even role. -/
def MassFail (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι)
    (f : OddRole n → Fin N) (v : EvenRole n) : Prop :=
  ∑ x, evenRowF M y₀ p t f v x < 1 / 2

/-- The conditional mass-failure probability at fixed tuples under independent odd-row sampling. -/
def massFailGiven (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι)
    (W : EvenRole n → Fin (kTup n) → Fin N) (v : EvenRole n) : ℝ :=
  ∑ f : OddRole n → Fin N, oddProdW M t W f * (if MassFail M y₀ p t f v then 1 else 0)

/-- The conditional raw mass-failure probability given the tags (11:346). -/
def rawFail (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι)
    (v : EvenRole n) : ℝ :=
  (rawTuples M y₀ t).expect fun W => massFailGiven M y₀ p t W v

/-! ## The tag stage (11:344–368) -/

/-- The first tag event at an outer word: the conditional raw failure probability of one of its even roles
exceeds `n^{-2P}` (11:347). -/
def T1 (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ) (t : OuterWord n → M.ι)
    (s : OuterWord n) : Prop :=
  ∃ v : EvenRole n, sliceOf v.1 = s ∧ (n : ℝ) ^ (-(2 * P)) < rawFail M y₀ p t v

/-- The number of outer neighbouring tags of high degree `d_G(x; π_{i(s^j)}) > .8`. -/
def highCount (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (t : OuterWord n → M.ι) (s : OuterWord n)
    (x : Fin N) : ℕ :=
  (Finset.univ.filter fun j : OuterCoord n => (4 / 5 : ℝ) < deg E M.G (piRow M y₀ (t (flipOuter s j))) x).card

/-- The second tag event: some label of the first support has more than half of its outer neighbouring tags of
high degree (11:348). -/
def T2 (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (t : OuterWord n → M.ι) (s : OuterWord n) : Prop :=
  ∃ x, (M.μ (t s)).w x ≠ 0 ∧ (Fintype.card (OuterCoord n) : ℝ) / 2 < highCount M y₀ t s x

/-- A tag event. -/
def TagBad (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ) (t : OuterWord n → M.ι)
    (s : OuterWord n) : Prop :=
  T1 M y₀ p P t s ∨ T2 M y₀ t s

/-- The tag law (11:354): raw tags conditioned on avoiding every tag event. -/
def tagLaw (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ) :
    FinProb (OuterWord n → M.ι) :=
  S07.condOr (rawTags M p) fun t => ∀ s, ¬ TagBad M y₀ p P t s

/-- The tag-stage local-lemma charge `4 n^{-2P}`. -/
def xTag (n : ℕ) (P : ℝ) : ℝ := 4 * (n : ℝ) ^ (-(2 * P))

/-- The local-lemma input for the tag events (11:350–354): each reads the tags of the radius-one outer ball. -/
def TagLLL11 (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ) : Prop :=
  S07.LLLInput (fun _ : OuterWord n => p) (fun s t => TagBad M y₀ p P t s) (fun s => wordBall s 1)
    (xTag n P) ((n + 1) ^ 2)

/-- Tags in the support of the raw law avoiding every tag event. -/
def GatedTags (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ)
    (t : OuterWord n → M.ι) : Prop :=
  (∀ s, p.w (t s) ≠ 0) ∧ ∀ s, ¬ TagBad M y₀ p P t s

/-- The comparison mean `A_s(y) = N π_{i(s)}(y)` (11:357). -/
def compA (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (t : OuterWord n → M.ι) (s : OuterWord n)
    (y : Fin N) : ℝ :=
  (N : ℝ) * piRow M y₀ (t s) y

/-- The comparison mean `B_s(x) = N α_{i(s)}(x) ∏_j d_G(x; π_{i(s^j)}) / D_x` (11:358–360). -/
def compB (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι)
    (s : OuterWord n) (x : Fin N) : ℝ :=
  (N : ℝ) * alphaRow M y₀ (t s) x *
    ∏ j : OuterCoord n, deg E M.G (piRow M y₀ (t (flipOuter s j))) x / deg E M.G (piBar M y₀ p) x

/-- Typical tags (11:366–368): both comparison means have average at most `C` over the outer words, for every
label. -/
def Typical11 (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (C : ℝ)
    (t : OuterWord n → M.ι) : Prop :=
  (∀ y, (Fintype.card (OuterWord n) : ℝ)⁻¹ * ∑ s, compA M y₀ t s y ≤ C) ∧
  (∀ x, (Fintype.card (OuterWord n) : ℝ)⁻¹ * ∑ s, compB M y₀ p t s x ≤ C)

/-- Separated moments under the tag law (11:364–368): removing the tag events touching the separated radius-one
balls costs `2` per word, and the raw means are `N π(z)` and `N Σ p_i α_i(z)`. -/
def TagMoment11 (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ) : Prop :=
  ∀ (z : Fin N) (m : ℕ), m ≤ n → ∀ s : Fin m → OuterWord n, (∀ i j, i ≠ j → 3 ≤ wordDist (s i) (s j)) →
    (tagLaw M y₀ p P).expect (fun t => ∏ i, compA M y₀ t (s i) z) ≤
        2 ^ m * ((N : ℝ) * piBar M y₀ p z) ^ m ∧
      (tagLaw M y₀ p P).expect (fun t => ∏ i, compB M y₀ p t (s i) z) ≤
        2 ^ m * ((N : ℝ) * alphaBar M y₀ p z) ^ m

/-! ## The tuple stage, odd loads and the clock (11:370–378) -/

/-- The tuple event at an even role: conditional mass-failure probability above `n^{-P}` (11:371). -/
def TupleBad (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ) (t : OuterWord n → M.ι)
    (v : EvenRole n) (W : EvenRole n → Fin (kTup n) → Fin N) : Prop :=
  (n : ℝ) ^ (-P) < massFailGiven M y₀ p t W v

/-- The tuple law at fixed tags: raw tuples conditioned on avoiding every tuple event. -/
def tupleLaw (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ) (t : OuterWord n → M.ι) :
    FinProb (EvenRole n → Fin (kTup n) → Fin N) :=
  S07.condOr (rawTuples M y₀ t) fun W => ∀ v, ¬ TupleBad M y₀ p P t v W

/-- The tuple-stage local-lemma charge `2 n^{-P}`. -/
def xTup (n : ℕ) (P : ℝ) : ℝ := 2 * (n : ℝ) ^ (-P)

/-- The local-lemma input for the tuple events (11:371): each reads the tuples within full-cube distance two. -/
def TupleLLL11 (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ)
    (t : OuterWord n → M.ι) : Prop :=
  S07.LLLInput (fun v : EvenRole n => tupLaw E M.G (M.μ (t (sliceOf v.1))) (y₀ (t (sliceOf v.1))) (kTup n))
    (fun v W => TupleBad M y₀ p P t v W) (fun v => evenBall v 2) (xTup n P) ((n + 1) ^ 4)

/-- The odd column sum at a second-side label. -/
def oddCol (M : Menu11 n N E X Y κ) (t : OuterWord n → M.ι) (W : EvenRole n → Fin (kTup n) → Fin N)
    (y : Fin N) : ℝ :=
  ∑ b : OddRole n, oddRowF M t W b y

/-- A successful tuple history: no tuple event and odd column sums at most `θ₀ = 10^{-8}` (11:375–378). -/
def GoodPre (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ) (t : OuterWord n → M.ι)
    (W : EvenRole n → Fin (kTup n) → Fin N) : Prop :=
  (∀ v, ¬ TupleBad M y₀ p P t v W) ∧ ∀ y, oddCol M t W y ≤ (1e-8 : ℝ)

/-- The clock output (Lemma 3.10 with `B = 4`, 11:377–378): injective odd labels avoiding every mass failure,
with joint upper comparison at most twice the product of the odd rows on at most `n^4` odd roles. -/
def ClockOK (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι)
    (W : EvenRole n → Fin (kTup n) → Fin N) (J : FinProb (OddRole n → Fin N)) : Prop :=
  (∀ f, J.w f ≠ 0 → Function.Injective f ∧ ∀ v, ¬ MassFail M y₀ p t f v) ∧
  ∀ (S : Finset (OddRole n)) (o : OddRole n → Fin N), (S.card : ℝ) ≤ (n : ℝ) ^ 4 →
    J.pr (fun f => ∀ b ∈ S, f b = o b) ≤ 2 * ∏ b ∈ S, oddRowF M t W b (o b)

/-- Separated odd-row moments under the tuple law (11:373–375). -/
def OddMoment11 (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ)
    (t : OuterWord n → M.ι) : Prop :=
  ∀ (y : Fin N) (m : ℕ), m ≤ n → ∀ b : Fin m → OddRole n,
    (∀ i j, i ≠ j → 3 ≤ HypercubeRamsey.hammingDist (b i).1 (b j).1) →
    (tupleLaw M y₀ p P t).expect (fun W => ∏ i, (N : ℝ) * oddRowF M t W (b i) y) ≤
      2 ^ m * ∏ i, compA M y₀ t (sliceOf (b i).1) y

/-! ## Even loads (11:380–394) -/

/-- The star mean (11:388–390): under raw tuples and independent odd rows, `N M_v(x)` integrates to `B_{s(v)}(x)`
(the internal weight to `N α_{i(s(v))}(x)`, each outer label to its degree into `π_{i(s^j)}`). -/
def StarMean11 (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι) : Prop :=
  ∀ (v : EvenRole n) (x : Fin N),
    (rawTuples M y₀ t).expect (fun W => ∑ f, oddProdW M t W f * ((N : ℝ) * evenRowF M y₀ p t f v x)) ≤
      compB M y₀ p t (sliceOf v.1) x

/-- The clock comparison for separated even stars (11:388): at a successful history the clock law is at most twice
the independent odd-row law on the at most `n²` neighbouring odd labels. -/
def ClockFactor11 (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ)
    (t : OuterWord n → M.ι) (J : (EvenRole n → Fin (kTup n) → Fin N) → FinProb (OddRole n → Fin N)) : Prop :=
  ∀ W, GoodPre M y₀ p P t W → ∀ (x : Fin N) (m : ℕ), m ≤ n → ∀ a : Fin m → EvenRole n,
    (∀ i j, i ≠ j → 5 ≤ HypercubeRamsey.hammingDist (a i).1 (a j).1) →
    ∑ f, (J W).w f * ∏ i, (N : ℝ) * evenRowF M y₀ p t f (a i) x ≤
      2 * ∑ f, oddProdW M t W f * ∏ i, (N : ℝ) * evenRowF M y₀ p t f (a i) x

/-- The tuple integral of separated star products (11:388–390): removing the tuple events touching the
radius-two scopes costs `2` per star, and the separated scopes integrate independently to the star means. -/
def EvenTupleIntegral11 (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ)
    (t : OuterWord n → M.ι) : Prop :=
  ∀ (x : Fin N) (m : ℕ), m ≤ n → ∀ a : Fin m → EvenRole n,
    (∀ i j, i ≠ j → 5 ≤ HypercubeRamsey.hammingDist (a i).1 (a j).1) →
    (tupleLaw M y₀ p P t).expect (fun W => ∑ f, oddProdW M t W f * ∏ i, (N : ℝ) * evenRowF M y₀ p t f (a i) x) ≤
      2 ^ m * ∏ i, compB M y₀ p t (sliceOf (a i).1) x

/-- Separated even-star moments under the tuple law and clock sampling (11:386–390). -/
def EvenMoment11 (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ)
    (t : OuterWord n → M.ι) (J : (EvenRole n → Fin (kTup n) → Fin N) → FinProb (OddRole n → Fin N)) : Prop :=
  ∀ (x : Fin N) (m : ℕ), m ≤ n → ∀ a : Fin m → EvenRole n,
    (∀ i j, i ≠ j → 5 ≤ HypercubeRamsey.hammingDist (a i).1 (a j).1) →
    ∑ W, (tupleLaw M y₀ p P t).w W *
        (if GoodPre M y₀ p P t W then ∑ f, (J W).w f * ∏ i, (N : ℝ) * evenRowF M y₀ p t f (a i) x else 0) ≤
      4 ^ m * ∏ i, compB M y₀ p t (sliceOf (a i).1) x

end

end HypercubeRamsey.S11.Core
