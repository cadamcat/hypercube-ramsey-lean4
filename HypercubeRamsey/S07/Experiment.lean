import HypercubeRamsey.S07.GridGeometry
import HypercubeRamsey.S07.CellFilters
import HypercubeRamsey.Framework.Props
import HypercubeRamsey.Framework.FinProbLemmas

/-!
# Lemma 7.1: the staged grid experiment

Source: `sections/07-…tex`, proof of Lemma 7.1 (lines 49–392); blueprint `research/blueprint/PART-B.md` §3.7.
Every object of the construction is an explicit finite formula of the geometry `Γ`, the finite menu `M` and the
tag profiles `Q`:

* tags `σ : Key → ι` and anchors `W : Cell → Fin N`; the raw law draws independent tags `σ g ∼ Q g` and,
  given the tags, independent anchors `W (g,t) ∼ μ_{σ g}` (07:70–72);
* the cell filters: cross validity in every cross order, own validity, the odd row `cellRow` (07:73–96), and
  the deletion laws `delRow` (07:98–114);
* tag events `TagBad` (07:163–171), the tag law (raw tags conditioned on avoiding them, 07:172–175);
* the star likelihood `starLik`, its marginal `starMarg`, the deletion reference `starRef`, predictive failure,
  alarm rates and alarms (07:196–245); the cell events `CellBad` and the anchor law (07:247–262);
* odd and even column sums, the posterior even rows (07:326–336) and their star integrals (07:363–371);
* the clock-sampler output property `ClockOK` (07:315–324).

Named facts (`RowLaw`, `DelCompare`, …, `GeomFacts`, `FilterFacts`, `TagLLL`, `AnchorLLL`, …) are the
conclusions of the nodes; a node that needs another node's conclusion takes it as a hypothesis, and the
assemblies in the later files supply it.
-/

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- The one-dimension hypothesis (7.1), with `c = d / 80`. -/
def Eq71At (D₀ d : ℝ) (n N : ℕ) (E : Fin N → Fin N → Prop)
    (X Y : Finset (Fin N)) : Prop :=
  ∀ σ τ : Law N, σ.SupportedIn X → τ.SupportedIn Y →
    σ.CapLE ((n : ℝ) ^ D₀) → τ.WidthLE ((n : ℝ) ^ ((1 : ℝ) / 4)) →
    ∀ col : Colour, (n : ℝ) ^ (-(d / 80)) < dens E col σ τ

/-- Even roles (placed on the first side). -/
abbrev EvenRole (n : ℕ) := {v : CubeVertex n // IsEvenRole v}

/-- Odd roles (placed on the second side). -/
abbrev OddRole (n : ℕ) := {v : CubeVertex n // ¬ IsEvenRole v}

/-- The odd neighbour of an even role across coordinate `j`. -/
def oddNbr {n : ℕ} (a : EvenRole n) (j : Fin n) : OddRole n :=
  ⟨cubeFlip a.1 j, fun h => ((cubeFlip_parity a.1 j).mp h) a.2⟩

/-- The odd labels seen by an even role, indexed by the flipped coordinate. -/
def nbrLabels {n N : ℕ} (f : OddRole n → Fin N) (a : EvenRole n) : Fin n → Fin N :=
  fun j => f (oddNbr a j)

/-- A finite menu retaining availability (07:51–53): one representative witness pair for each successful
support pair.  The fields are exactly what availability of `PGridPure G d p` on `(X, Y)` provides. -/
structure Menu7 (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X Y : Finset (Fin N))
    (d p κ : ℝ) where
  ι : Type
  [fin : Fintype ι]
  μ : ι → Law N
  ν : ι → Law N
  μ_supp : ∀ i, (μ i).SupportedIn X
  ν_supp : ∀ i, (ν i).SupportedIn Y
  pure : ∀ i, PGridPure G d p n N E (μ i) (ν i)
  avail : ∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N → (RY.card : ℝ) ≤ κ * N →
    ∃ i, (∀ x ∈ RX, (μ i).w x = 0) ∧ (∀ y ∈ RY, (ν i).w y = 0)

attribute [instance] Menu7.fin

/-- Conditioning on an event, keeping the law when the event has mass zero. -/
noncomputable def condOr {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) : FinProb Ω :=
  if h : 0 < P.pr A then P.cond A h else P

/-- The law filtered to common neighbours of a list, normalized; the law itself when the mass is zero. -/
noncomputable def filtLaw {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (ν : Law N)
    (L : List (Fin N)) : Law N :=
  if h : 0 < filterMass E G ν L then
    { w := filt E G ν L
      nonneg := (filt_probability_and_support E G ν L h).1
      sum_eq_one := (filt_probability_and_support E G ν L h).2.1 }
  else ν

/-- The cell-row cap `L = exp(n^{d/2} + 2cs log n + 1)`, `c = d/80` (07:95). -/
noncomputable def cellCap (d : ℝ) (n s : ℕ) : ℝ :=
  Real.exp ((n : ℝ) ^ (d / 2) + 2 * (d / 80) * (s : ℝ) * Real.log (n : ℝ) + 1)

/-- The local-lemma charge `n^{-D₀/4}` (07:174, 258). -/
noncomputable def xL (D₀ : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-(D₀ / 4))

section Experiment

variable {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
  {p κ : ℝ}
variable (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)

/-! ## Cell filters (07:73–114) -/

/-- Cross validity (07:84–88) of the cell with key `g`, tag `i` and cross anchor labels `a h`: in every cross
order (the key `h₀` last) each successive restriction keeps a fraction at least `n^{-c}`, `c = d/80`.  The empty
cross list is allowed. -/
def CrossValidRow (i : M.ι) (a : Γ.Key → Fin N) (g : Γ.Key) : Prop :=
  ∀ h₀ ∈ Γ.crossKeys g, ∀ k < (Γ.crossKeys g).length,
    (n : ℝ) ^ (-(d / 80)) * filterMass E G (M.ν i) (((Γ.crossOrder g h₀).map a).take k) ≤
      filterMass E G (M.ν i) (((Γ.crossOrder g h₀).map a).take (k + 1))

/-- Labels of the cross list of a cell. -/
noncomputable def crossLabels (W : Γ.Cell → Fin N) (c : Γ.Cell) : List (Fin N) :=
  (Γ.crossNames c.1 c.2).map W

/-- Labels of all listed anchors of a cell (cross list, then own list). -/
noncomputable def cellLabels (W : Γ.Cell → Fin N) (c : Γ.Cell) : List (Fin N) :=
  (Γ.fullNames c).map W

/-- Own validity (07:88–89): after the full cross restriction the own list keeps a fraction `≥ 1 - n^{-2}`. -/
def OwnValid (i : M.ι) (W : Γ.Cell → Fin N) (c : Γ.Cell) : Prop :=
  (1 - (n : ℝ) ^ (-2 : ℝ)) * filterMass E G (M.ν i) (crossLabels Γ W c) ≤
    filterMass E G (M.ν i) (cellLabels Γ W c)

/-- Validity of the odd cell `c` under tags `σ` and anchors `W` (07:89–90). -/
def CellValid (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (c : Γ.Cell) : Prop :=
  CrossValidRow Γ M (σ c.1) (fun h => W (h, c.2)) c.1 ∧ OwnValid Γ M (σ c.1) W c

/-- The odd row `p_{g,t}` (07:90–92): the normalized fully restricted second law on validity, zero otherwise. -/
noncomputable def cellRow (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (c : Γ.Cell) (y : Fin N) : ℝ :=
  if CellValid Γ M σ W c then filt E G (M.ν (σ c.1)) (cellLabels Γ W c) y else 0

/-- The deletion law `p^{(-w)}` of the named anchor `w` (07:98–102): the second law restricted to hits of the
listed anchors with one copy of `w`'s label removed, normalized; the second law itself at zero mass.  The label
set of the erased list is that of the other names, so the law does not read `W w` (node `delRow_update`). -/
noncomputable def delRow (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (c w : Γ.Cell) : Law N :=
  filtLaw E G (M.ν (σ c.1)) ((cellLabels Γ W c).erase (W w))

/-- The retained fraction behind a deletion comparison (07:103–110): `1 - n^{-2}` for an own name, `(1 - n^{-2})
n^{-c}` for a cross name. -/
noncomputable def delTheta (c w : Γ.Cell) : ℝ :=
  if w.1 = c.1 then 1 - (n : ℝ) ^ (-2 : ℝ) else (1 - (n : ℝ) ^ (-2 : ℝ)) * (n : ℝ) ^ (-(d / 80))

/-! ## Raw laws and tag events (07:70–72, 116–175) -/

/-- Raw anchors given the tags: independent `W c ∼ μ_{σ c.1}` (07:71–72). -/
noncomputable def rawAnchors (σ : Γ.Key → M.ι) : FinProb (Γ.Cell → Fin N) :=
  FinProb.pi fun c : Γ.Cell => M.μ (σ c.1)

/-- The cross-failure probability at key `g` given all tags (07:163–166).  It is computed with one raw anchor
per key; it equals the cross-failure probability of every cell `(g, t)` (node `cell_invalid_prob`). -/
noncomputable def crossFailKey (σ : Γ.Key → M.ι) (g : Γ.Key) : ℝ :=
  (FinProb.pi fun h : Γ.Key => M.μ (σ h)).pr fun a => ¬ CrossValidRow Γ M (σ g) a g

/-- The tag event `B_g` (07:163–167). -/
def TagBad (D₀ : ℝ) (σ : Γ.Key → M.ι) (g : Γ.Key) : Prop :=
  (n : ℝ) ^ (-(D₀ / 2)) < crossFailKey Γ M σ g

/-- The tag law (07:172–175): raw tags conditioned on avoiding every `B_g`. -/
noncomputable def tagLaw (Q : Γ.Key → FinProb M.ι) (D₀ : ℝ) : FinProb (Γ.Key → M.ι) :=
  condOr (FinProb.pi Q) fun σ => ∀ g, ¬ TagBad Γ M D₀ σ g

/-- The raw mean of a cell row under raw tags and raw anchors (07:116–122). -/
noncomputable def rawRowMean (Q : Γ.Key → FinProb M.ι) (c : Γ.Cell) (y : Fin N) : ℝ :=
  (FinProb.pi Q).expect fun σ => (rawAnchors Γ M σ).expect fun W => cellRow Γ M σ W c y

/-- Tag profiles (07:116–122): (i) bounded mean first laws at every key; (ii) bounded mean odd rows, averaged
over the auxiliary words (equivalently over the odd sites with that grid key). -/
structure Profiles7 (K : ℝ) where
  Q : Γ.Key → FinProb M.ι
  mu_mean : ∀ g x, (N : ℝ) * ∑ i, (Q g).w i * (M.μ i).w x ≤ K
  row_mean : ∀ g y,
    (N : ℝ) * (((2 : ℝ) ^ q)⁻¹ * ∑ t : Γ.AuxWord, rawRowMean Γ M Q (g, t) y) ≤ K

/-! ## Predictive alarms and cell events (07:196–262) -/

/-- `F_z(y)` at an even vertex `v` (07:203): the product of the neighbouring odd rows with the anchor of `v`'s
cell replaced by `z`.  Rows are zero on invalid cells, so the validity indicator is built in. -/
noncomputable def starLik (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (v : CubeVertex n) (z : Fin N)
    (y : Fin n → Fin N) : ℝ :=
  ∏ j, cellRow Γ M σ (Function.update W (Γ.key v) z) (Γ.key (cubeFlip v j)) (y j)

/-- `M_v(y)` (07:204). -/
noncomputable def starMarg (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (v : CubeVertex n)
    (y : Fin n → Fin N) : ℝ :=
  ∑ z, (M.μ (σ (Γ.key v).1)).w z * starLik Γ M σ W v z y

/-- `Q_v(y)` (07:207–210): the product of the neighbouring deletion laws for the name of `v`'s cell. -/
noncomputable def starRef (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (v : CubeVertex n)
    (y : Fin n → Fin N) : ℝ :=
  ∏ j, (delRow Γ M σ W (Γ.key (cubeFlip v j)) (Γ.key v)).w (y j)

/-- Predictive failure (07:216–217). -/
def PredFail (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (v : CubeVertex n) (y : Fin n → Fin N) : Prop :=
  starMarg Γ M σ W v y = 0 ∨
    starMarg Γ M σ W v y < Real.exp (-(4 / 100 : ℝ) * q) * starRef Γ M σ W v y

/-- The alarm rate `r_v` (07:219–222): the probability of predictive failure under independent neighbour
draws from the actual rows, zero when a neighbouring row is invalid. -/
noncomputable def alarmRate (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (v : CubeVertex n) : ℝ :=
  ∑ y : Fin n → Fin N, (∏ j, cellRow Γ M σ W (Γ.key (cubeFlip v j)) (y j)) *
    (if PredFail Γ M σ W v y then 1 else 0)

/-- An alarm at the cell `c` (07:233–235): some even role reading `c` has `r_v > e^{-.02q}`. -/
def Alarm (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (c : Γ.Cell) : Prop :=
  ∃ a : EvenRole n, Γ.key a.1 = c ∧ Real.exp (-(2 / 100 : ℝ) * q) < alarmRate Γ M σ W a.1

/-- The grouped bad event of a cell (07:248–250): filter failure or an alarm. -/
def CellBad (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (c : Γ.Cell) : Prop :=
  ¬ CellValid Γ M σ W c ∨ Alarm Γ M σ W c

/-- The anchor law at fixed tags (07:259–262): raw anchors conditioned on avoiding every cell event. -/
noncomputable def anchorLaw (σ : Γ.Key → M.ι) : FinProb (Γ.Cell → Fin N) :=
  condOr (rawAnchors Γ M σ) fun W => ∀ c, ¬ CellBad Γ M σ W c

/-! ## Column sums, posterior rows and typical tags (07:177–194, 264–391) -/

/-- The odd column sum at a second-side label (07:305–307). -/
noncomputable def oddColumn (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (y : Fin N) : ℝ :=
  ∑ u : OddRole n, cellRow Γ M σ W (Γ.key u.1) y

/-- The posterior even row `p_v^X` at neighbour data `y` (07:326–331). -/
noncomputable def evenRowAt (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (a : EvenRole n)
    (y : Fin n → Fin N) (x : Fin N) : ℝ :=
  starLik Γ M σ W a.1 x y * (M.μ (σ (Γ.key a.1).1)).w x / starMarg Γ M σ W a.1 y

/-- The posterior even row at the odd assignment `f`. -/
noncomputable def evenRow (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (f : OddRole n → Fin N)
    (a : EvenRole n) (x : Fin N) : ℝ :=
  evenRowAt Γ M σ W a (nbrLabels f a) x

/-- The even column sum at a first-side label (07:389–390). -/
noncomputable def evenColumn (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (f : OddRole n → Fin N)
    (x : Fin N) : ℝ :=
  ∑ a : EvenRole n, evenRow Γ M σ W f a x

/-- The star integral of one even role (07:363–371): independent neighbour draws from the actual rows,
predictive success retained, times the normalized even row at `x`. -/
noncomputable def evenStar (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (a : EvenRole n) (x : Fin N) : ℝ :=
  ∑ y : Fin n → Fin N, (∏ j, cellRow Γ M σ W (Γ.key (cubeFlip a.1 j)) (y j)) *
    ((if PredFail Γ M σ W a.1 y then 0 else 1) * ((N : ℝ) * evenRowAt Γ M σ W a y x))

/-- Typical tags (07:191–194): bounded normalized average first-side loads at every label. -/
def Typical (C : ℝ) (σ : Γ.Key → M.ι) : Prop :=
  ∀ x, (Fintype.card (EvenRole n) : ℝ)⁻¹ *
    ∑ a : EvenRole n, (N : ℝ) * (M.μ (σ (Γ.key a.1).1)).w x ≤ C

/-- A successful prehistory (07:315): no cell event and odd column sums at most `θ₀ = 10⁻⁸`. -/
def GoodPre (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) : Prop :=
  (∀ c, ¬ CellBad Γ M σ W c) ∧ ∀ y, oddColumn Γ M σ W y ≤ (1e-8 : ℝ)

/-- The clock-sampler output (07:315–324, Lemma 3.10 with `B = 3`): injective odd labels avoiding every
predictive failure, with joint upper comparison at most twice the product of the odd rows on sets of at most
`n^3` odd roles. -/
def ClockOK (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (J : FinProb (OddRole n → Fin N)) : Prop :=
  (∀ f, J.w f ≠ 0 → Function.Injective f ∧
      ∀ a : EvenRole n, ¬ PredFail Γ M σ W a.1 (nbrLabels f a)) ∧
    ∀ (S : Finset (OddRole n)) (o : OddRole n → Fin N), (S.card : ℝ) ≤ (n : ℝ) ^ 3 →
      J.pr (fun f => ∀ u ∈ S, f u = o u) ≤ 2 * ∏ u ∈ S, cellRow Γ M σ W (Γ.key u.1) (o u)

end Experiment

/-! ## The local lemma interface -/

/-- Replace the coordinates in `U` of `ω` by `a`. -/
noncomputable def glue {V : Type*} {α : V → Type*} (U : Finset V) (ω : ∀ v, α v) (a : ∀ v : U, α v) : ∀ v, α v :=
  fun v => if h : v ∈ U then a ⟨v, h⟩ else ω v

/-- Local-lemma input on a product law (Lemma 3.4 with independent variables): scopes, dependency degree at
most `Δ` (events adjacent when their scopes meet), and probabilities at most `x (1 - x)^Δ`. -/
structure LLLInput {V : Type} [Fintype V] [DecidableEq V] {α : V → Type} [∀ v, Fintype (α v)]
    (P : ∀ v, FinProb (α v)) {I : Type} [Fintype I] (Bad : I → (∀ v, α v) → Prop)
    (sc : I → Finset V) (x : ℝ) (Δ : ℕ) : Prop where
  x_nonneg : 0 ≤ x
  x_lt_one : x < 1
  scope : ∀ i, FinProb.DependsOn (Bad i) (sc i)
  degree : ∀ i, (Finset.univ.filter fun j => j ≠ i ∧ ¬ Disjoint (sc i) (sc j)).card ≤ Δ
  prob : ∀ i, (FinProb.pi P).pr (Bad i) ≤ x * (1 - x) ^ Δ

/-- Conditional avoidance on a product law with free coordinates (Lemma 3.4 and its independent-variables
case, as used at 07:184–190, 280–289, 354–357): the avoidance event has positive mass, and conditioning on it
costs at most `(1 - x)^{-#T}` against any bound `B` for the integral over the coordinates `U`, where `T` is the
set of events whose scopes meet `U`. -/
def CondProductBound : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {α : V → Type} [∀ v, Fintype (α v)]
    [∀ v, DecidableEq (α v)] (P : ∀ v, FinProb (α v)) {I : Type} [Fintype I] [DecidableEq I]
    (Bad : I → (∀ v, α v) → Prop) (sc : I → Finset V) (x : ℝ) (Δ : ℕ),
    LLLInput P Bad sc x Δ →
      0 < (FinProb.pi P).pr (fun ω => ∀ i, ¬ Bad i ω) ∧
      ∀ (U : Finset V) (Φ : (∀ v, α v) → ℝ), (∀ ω, 0 ≤ Φ ω) → ∀ B : ℝ,
        (∀ ω, ∑ a : (∀ v : U, α v), (∏ v : U, (P v).w (a v)) * Φ (glue U ω a) ≤ B) →
        (condOr (FinProb.pi P) (fun ω => ∀ i, ¬ Bad i ω)).expect Φ ≤
          ((1 - x) ^ (Finset.univ.filter fun i => ¬ Disjoint (sc i) U).card)⁻¹ * B

/-- Lemma 3.3's balanced mixture with subprobability second outputs (07:123–132): a menu whose second outputs
`v i` are subprobabilities vanishing wherever the menu's availability removes labels has a mixture with all
expected atoms at most `4 / (κ N)`. -/
def BalancedSub : Prop :=
  ∀ {N : ℕ}, 0 < N → ∀ {ι : Type} [Fintype ι] (μ : ι → Law N) (v : ι → Fin N → ℝ) (κ : ℝ), 0 < κ →
    (∀ i y, 0 ≤ v i y) → (∀ i, ∑ y, v i y ≤ 1) →
    (∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N → (RY.card : ℝ) ≤ κ * N →
      ∃ i, (∀ x ∈ RX, (μ i).w x = 0) ∧ (∀ y ∈ RY, v i y = 0)) →
    ∃ t : FinProb ι, (∀ x, ∑ i, t.w i * (μ i).w x ≤ 4 / (κ * N)) ∧
      (∀ y, ∑ i, t.w i * v i y ≤ 4 / (κ * N))

section Facts

variable {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
  {p κ : ℝ}
variable (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)

/-! ## Geometry facts (L7.1a) -/

/-- Local geometry (07:61–63, 79–82, 211–214, 235–237). -/
structure GeomLocal : Prop where
  names_adj : ∀ u v : CubeVertex n, (cube n).Adj u v → Γ.key v ∈ Γ.fullNames (Γ.key u)
  flip_dist : ∀ (v : CubeVertex n) j, Γ.cellDist (Γ.key v) (Γ.key (cubeFlip v j)) ≤ 1
  cross_count : ∀ v : CubeVertex n,
    (Finset.univ.filter fun j => (Γ.key (cubeFlip v j)).1 ≠ (Γ.key v).1).card ≤ s * ℓ
  keyNbrs_card : ∀ g, (Γ.keyNbrs g).card ≤ 2 * s
  auxBall_one_card : ∀ t, (Γ.auxBall t 1).card = q + 1
  fullNames_nodup : ∀ c, (Γ.fullNames c).Nodup

/-- Ball sizes in the grid, auxiliary and grid-times-auxiliary graphs (07:172, 253, 283, 355). -/
structure GeomBalls : Prop where
  keyBall_card : ∀ g R, ((Γ.keyBall g R).card : ℝ) ≤ (2 * s + 1 : ℝ) ^ R
  auxBall_card : ∀ t R, ((Γ.auxBall t R).card : ℝ) ≤ (q + 1 : ℝ) ^ R
  cellBall_card : ∀ c R, ((Γ.cellBall c R).card : ℝ) ≤ (2 * s + q + 1 : ℝ) ^ R

/-- Exact cell counts in each parity class (07:65–68): the auxiliary word is uniform on either parity, also when
the grid key is fixed. -/
structure GeomCounts : Prop where
  even_card : Fintype.card (EvenRole n) = 2 ^ (n - 1)
  odd_card : Fintype.card (OddRole n) = 2 ^ (n - 1)
  even_count : ∀ c : Γ.Cell, ((Finset.univ.filter fun a : EvenRole n => Γ.key a.1 = c).card : ℝ) =
    (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass c.1
  odd_count : ∀ c : Γ.Cell, ((Finset.univ.filter fun u : OddRole n => Γ.key u.1 = c).card : ℝ) =
    (Fintype.card (OddRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass c.1
  keyMass_sum : ∑ g, Γ.keyMass g = 1
  keyMass_le : ∀ g, Γ.keyMass g ≤ (2 * (n : ℝ) ^ (-(d / 4))) ^ s

/-- Near fractions for the three scattered-moment estimates (07:183, 273–274, 341–345). -/
structure GeomNear : Prop where
  even_sameKey : ∀ a : EvenRole n,
    ((Finset.univ.filter fun a' : EvenRole n => (Γ.key a'.1).1 = (Γ.key a.1).1).card : ℝ) ≤
      (2 * (n : ℝ) ^ (-(d / 4))) ^ s * Fintype.card (EvenRole n)
  odd_nearKey : ∀ u : OddRole n,
    ((Finset.univ.filter fun u' : OddRole n => Γ.keyDist (Γ.key u'.1).1 (Γ.key u.1).1 ≤ 2).card : ℝ) ≤
      (2 * s + 1 : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(d / 4))) ^ s * Fintype.card (OddRole n)
  even_nearAux : ∀ a : EvenRole n,
    ((Finset.univ.filter fun a' : EvenRole n => Γ.auxDist (Γ.key a'.1).2 (Γ.key a.1).2 ≤ 5).card : ℝ) ≤
      (q + 1 : ℝ) ^ 5 * ((2 : ℝ) ^ q)⁻¹ * Fintype.card (EvenRole n)

/-- All geometry facts of L7.1a. -/
structure GeomFacts : Prop where
  loc : GeomLocal Γ
  balls : GeomBalls Γ
  counts : GeomCounts Γ
  near : GeomNear Γ

/-! ## Filter facts (L7.1b, L7.1f(i), L7.1h) -/

/-- L7.1b(i): rows are nonnegative subprobabilities supported on hits of their listed anchors and on the second
law, probabilities on valid cells. -/
def RowLaw : Prop :=
  ∀ σ W c, (∀ y, 0 ≤ cellRow Γ M σ W c y) ∧ (∑ y, cellRow Γ M σ W c y ≤ 1) ∧
    (CellValid Γ M σ W c → ∑ y, cellRow Γ M σ W c y = 1) ∧
    ∀ y, cellRow Γ M σ W c y ≠ 0 →
      passesAnchors E G (cellLabels Γ W c) y ∧ (M.ν (σ c.1)).w y ≠ 0

/-- L7.1b(ii): `N p_{g,t} ≤ L` (07:94–95). -/
def RowCap : Prop :=
  ∀ σ W c y, (N : ℝ) * cellRow Γ M σ W c y ≤ cellCap d n s

/-- L7.1b(iii): deletion comparisons on validity (07:103–113). -/
def DelCompare : Prop :=
  ∀ σ W c w, CellValid Γ M σ W c → w ∈ Γ.fullNames c → ∀ y,
    cellRow Γ M σ W c y ≤ (delTheta Γ c w)⁻¹ * (delRow Γ M σ W c w).w y

/-- L7.1b(iii): a deletion law does not read its deleted variable (07:101–102, 114). -/
def DelUpdate : Prop :=
  ∀ σ W c w z, w ∈ Γ.fullNames c →
    delRow Γ M σ (Function.update W w z) c w = delRow Γ M σ W c w

/-- `Q_v` does not depend on the anchor of `v`'s cell (07:209–210). -/
def StarRefUpdate : Prop :=
  ∀ σ W (v : CubeVertex n) z,
    starRef Γ M σ (Function.update W (Γ.key v) z) v = starRef Γ M σ W v

/-- L7.1f(i): `F_z ≤ exp(c m log n + 2/n) Q_v` with `m = sℓ` special bits (07:211–214). -/
def StarLikBound : Prop :=
  ∀ σ W (v : CubeVertex n) z y, starLik Γ M σ W v z y ≤
    Real.exp ((d / 80) * ((s * ℓ : ℕ) : ℝ) * Real.log n + 2 / n) * starRef Γ M σ W v y

/-- L7.1h: on predictive success the posterior even row is a probability law on the common neighbours of the
odd labels (07:326–332). -/
def EvenRowLaw : Prop :=
  ∀ σ W (f : OddRole n → Fin N) (a : EvenRole n), ¬ PredFail Γ M σ W a.1 (nbrLabels f a) →
    (∀ x, 0 ≤ evenRow Γ M σ W f a x) ∧ (∑ x, evenRow Γ M σ W f a x = 1) ∧
    ∀ x, evenRow Γ M σ W f a x ≠ 0 → ∀ b : OddRole n, (cube n).Adj a.1 b.1 → Hits E G x (f b)

/-- L7.1h: `N p_v^X ≤ e^{.06q}` on predictive success (07:333–335). -/
def EvenRowCap : Prop :=
  ∀ σ W (a : EvenRole n) y, ¬ PredFail Γ M σ W a.1 y →
    ∀ x, (N : ℝ) * evenRowAt Γ M σ W a y x ≤ Real.exp ((6 / 100 : ℝ) * q)

/-- All deterministic filter facts. -/
structure FilterFacts : Prop where
  row_law : RowLaw Γ M
  row_cap : RowCap Γ M
  del_compare : DelCompare Γ M
  del_update : DelUpdate Γ M
  starRef_update : StarRefUpdate Γ M
  starLik_bound : StarLikBound Γ M
  evenRow_law : EvenRowLaw Γ M
  evenRow_cap : EvenRowCap Γ M

/-! ## Stage facts -/

/-- The local-lemma input for the tag events (07:167–175). -/
def TagLLL (Q : Γ.Key → FinProb M.ι) (D₀ : ℝ) : Prop :=
  LLLInput Q (fun g σ => TagBad Γ M D₀ σ g) (fun g => Γ.keyBall g 1) (xL D₀ n) ((2 * s + 1) ^ 2)

/-- The local-lemma input for the cell events at fixed tags (07:247–259). -/
def AnchorLLL (D₀ : ℝ) (σ : Γ.Key → M.ι) : Prop :=
  LLLInput (fun c : Γ.Cell => M.μ (σ c.1)) (fun c W => CellBad Γ M σ W c)
    (fun c => Γ.cellBall c 2) (xL D₀ n) ((2 * s + q + 1) ^ 4)

/-- L7.1d at a cell: raw cell failure is cross failure plus own failure (07:150–161). -/
def CellInvalidBound (σ : Γ.Key → M.ι) : Prop :=
  ∀ c, (rawAnchors Γ M σ).pr (fun W => ¬ CellValid Γ M σ W c) ≤
    crossFailKey Γ M σ c.1 + (n : ℝ) ^ 2 * ((q : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p)

/-- L7.1f(ii): the mean alarm rate over the anchor of the role's cell (07:224–228). -/
def AlarmMean : Prop :=
  ∀ σ W (a : EvenRole n), ∑ z, (M.μ (σ (Γ.key a.1).1)).w z *
    alarmRate Γ M σ (Function.update W (Γ.key a.1) z) a.1 ≤ Real.exp (-(4 / 100 : ℝ) * q)

/-- L7.1f(iii): at most `(n+1)^{2s+1}` alarm formulas per cell (07:233–240). -/
def AlarmReps : Prop :=
  ∀ c : Γ.Cell, ∃ S : Finset (EvenRole n), S.card ≤ (n + 1) ^ (2 * s + 1) ∧
    (∀ a ∈ S, Γ.key a.1 = c) ∧
    ∀ a : EvenRole n, Γ.key a.1 = c → ∃ a' ∈ S, ∀ σ W, alarmRate Γ M σ W a.1 = alarmRate Γ M σ W a'.1

/-- L7.1f: the alarm probability of one cell over its anchor, uniformly in everything else (07:240–245). -/
def AlarmProb (σ : Γ.Key → M.ι) : Prop :=
  ∀ W c, ∑ z, (M.μ (σ c.1)).w z * (if Alarm Γ M σ (Function.update W c z) c then 1 else 0) ≤
    ((n : ℝ) + 1) ^ (2 * s + 1) * Real.exp (-(2 / 100 : ℝ) * q)

/-- L7.1g: separated odd-role products under the two-stage law (07:280–298). -/
def OddMoment (Q : Γ.Key → FinProb M.ι) (D₀ : ℝ) : Prop :=
  ∀ (y : Fin N) (m : ℕ), m ≤ n → ∀ u : Fin m → OddRole n,
    (∀ i j, i ≠ j → 3 ≤ Γ.keyDist (Γ.key (u i).1).1 (Γ.key (u j).1).1) →
    (FinProb.bind (tagLaw Γ M Q D₀) (anchorLaw Γ M)).expect
        (fun ω => ∏ i, (N : ℝ) * cellRow Γ M ω.1 ω.2 (Γ.key (u i).1) y) ≤
      4 ^ m * ∏ i, (N : ℝ) * rawRowMean Γ M Q (Γ.key (u i).1) y

/-- L7.1i: the star cancellation at one role (07:363–373). -/
def StarCancel (σ : Γ.Key → M.ι) : Prop :=
  ∀ W (a : EvenRole n) x, ∑ z, (M.μ (σ (Γ.key a.1).1)).w z *
    evenStar Γ M σ (Function.update W (Γ.key a.1) z) a x ≤ (N : ℝ) * (M.μ (σ (Γ.key a.1).1)).w x

/-- L7.1i: the clock comparison at a successful prehistory, for separated even roles (07:347–352). -/
def ClockFactor (σ : Γ.Key → M.ι) (J : (Γ.Cell → Fin N) → FinProb (OddRole n → Fin N)) : Prop :=
  ∀ W, GoodPre Γ M σ W → ∀ (x : Fin N) (m : ℕ), m ≤ n → ∀ a : Fin m → EvenRole n,
    (∀ i j, i ≠ j → 6 ≤ Γ.auxDist (Γ.key (a i).1).2 (Γ.key (a j).1).2) →
    ∑ f, (J W).w f * ∏ i, (N : ℝ) * evenRow Γ M σ W f (a i) x ≤ 2 * ∏ i, evenStar Γ M σ W (a i) x

/-- L7.1i: the anchor integral of separated star integrals (07:354–380). -/
def EvenAnchorIntegral (σ : Γ.Key → M.ι) : Prop :=
  ∀ (x : Fin N) (m : ℕ), m ≤ n → ∀ a : Fin m → EvenRole n,
    (∀ i j, i ≠ j → 6 ≤ Γ.auxDist (Γ.key (a i).1).2 (Γ.key (a j).1).2) →
    (anchorLaw Γ M σ).expect (fun W => ∏ i, evenStar Γ M σ W (a i) x) ≤
      2 ^ m * ∏ i, (N : ℝ) * (M.μ (σ (Γ.key (a i).1).1)).w x

/-- L7.1i: separated even-role products under anchors and clock sampling (07:375–380). -/
def EvenMoment (σ : Γ.Key → M.ι) (J : (Γ.Cell → Fin N) → FinProb (OddRole n → Fin N)) : Prop :=
  ∀ (x : Fin N) (m : ℕ), m ≤ n → ∀ a : Fin m → EvenRole n,
    (∀ i j, i ≠ j → 6 ≤ Γ.auxDist (Γ.key (a i).1).2 (Γ.key (a j).1).2) →
    ∑ W, (anchorLaw Γ M σ).w W *
        (if GoodPre Γ M σ W then ∑ f, (J W).w f * ∏ i, (N : ℝ) * evenRow Γ M σ W f (a i) x else 0) ≤
      4 ^ m * ∏ i, (N : ℝ) * (M.μ (σ (Γ.key (a i).1).1)).w x

end Facts

end HypercubeRamsey.S07
