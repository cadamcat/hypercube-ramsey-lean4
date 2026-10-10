import HypercubeRamsey.S04.KeyGadget
import HypercubeRamsey.Framework.Embedding
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.Tools.CubeGeometry

/-!
# Lemma 4.1 core: the staged experiment (D4.3–D4.7)

Source: `sections/04-…tex`, proof of Lemma 4.1, Steps 2–7 (lines 89–598).  Every object of the construction is an
explicit finite formula of the input menu `M`, the patch tags `tag : Key → ι` and the mask profiles `q, q'`:

* the preparatory sample `Prep`: D3.8 positions, activations and ties for the height device on the even sites,
  a mask `M_{c,κ}` and a tuple `W_{c,κ}` for every center ID `c` and key `κ`, and an odd mask `M'_u` for every
  odd role (04:181–190); its law `prepLaw q q'` (masks from the profiles, tuples i.i.d. from the masked first
  laws given the masks, positions/activations/ties from D3.8);
* retained masses, validity of ID sets at odd roles, the greedy marking and eligibility (04:206–233, 300–309);
* the long-rule selection `sel`, the odd rows `oddRow` (normalized filtered second laws on valid sets, zero
  otherwise) and their sampling laws `oddDraw` with fallback (04:340–352);
* the local event `EvLocal`, the likelihood `lik` (every rule recomputed after replacing the tuple of the
  selected ID), its marginal `marg`, the deleted-tuple reference `refProd`, the predictive gate `PredOK`, the
  common neighbourhood `comm` and the even rows `evenRowAt` (04:354–432);
* geometric success `GeoSucc`, the pre-injection event `SPre`, the injection-law property `InjOK`, column sums,
  raw expected rows, locality (`AgreeOn`, `LocalTo`) and separation (04:437–597).

Named facts (`KeyNbrCard`, …, `EvenClock`) are the conclusions of the nodes; a node that needs another node's
conclusion takes it as a hypothesis, and the assemblies supply it.
-/

namespace HypercubeRamsey.S04

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-! ## Roles and neighbourhoods -/

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

/-- The even sites of `Q_n` (the queried sites of the height device, 04:169–170). -/
noncomputable def evenSites (n : ℕ) : Finset (CubeVertex n) := Finset.univ.filter IsEvenRole

/-- The (even) neighbours of an odd role. -/
noncomputable def oddAdj {n : ℕ} (u : OddRole n) : Finset (CubeVertex n) :=
  Finset.univ.filter fun v => (cube n).Adj u.1 v

/-- The Hamming ball of radius `R`. -/
noncomputable def ballV {n : ℕ} (v : CubeVertex n) (R : ℕ) : Finset (CubeVertex n) :=
  Finset.univ.filter fun w => _root_.hammingDist v w ≤ R

/-- `Z_u = {g(v) : v ∼ u}` (04:134–135). -/
noncomputable def Zset (β γ : ℝ) {n : ℕ} (u : OddRole n) : Finset (Key β γ n) :=
  (oddAdj u).image (key β γ n)

/-! ## Inputs -/

/-- The body of `PrepLaw` with its witnesses `sX, sY, p` explicit (04:55–80). -/
def PrepAt (β γ : ℝ) (G : Colour) (n N : ℕ) (E : Fin N → Fin N → Prop) (μ ν : Law N)
    (sX sY p : ℝ) : Prop :=
  (n : ℝ) ^ β ≤ sX ∧ sX ≤ 3 / 2 * (n : ℝ) ^ β ∧
    (n : ℝ) ^ γ ≤ sY ∧ sY ≤ 3 / 2 * (n : ℝ) ^ γ ∧
    μ.WidthLE sX ∧ ν.WidthLE (sY + 1) ∧
    1 / 2 + (n : ℝ) ^ (-h4 β γ) ≤ p ∧
    (∀ y, ν.w y ≠ 0 → p - (n : ℝ) ^ (-(omega4 β γ) / 5) ≤ dens E G μ (Law.dirac y)) ∧
    (∀ μ' ν' : Law N,
      (∀ x, μ.w x = 0 → μ'.w x = 0) →
      (∀ y, ν.w y = 0 → ν'.w y = 0) →
      μ'.WidthLE (sX + (n : ℝ) ^ (β - omega4 β γ / 2) / 2) →
      ν'.WidthLE (sY + (n : ℝ) ^ (γ - omega4 β γ / 2) / 2) →
      dens E G μ' ν' ≤ p + (n : ℝ) ^ (-(omega4 β γ) / 3))

theorem prepLaw_iff {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {μ ν : Law N} :
    PrepLaw β γ G n N E μ ν ↔ ∃ sX sY p, PrepAt β γ G n N E μ ν sX sY p := Iff.rfl

/-- The prepared menu of L4.1-core: patches `(μ i, ν i)` with their plateau witnesses, supported in `X`, `Y`. -/
structure Menu4 (β γ : ℝ) (G : Colour) (n N : ℕ) (E : Fin N → Fin N → Prop)
    (X Y : Finset (Fin N)) where
  ι : Type
  [fin : Fintype ι]
  μ : ι → Law N
  ν : ι → Law N
  sX : ι → ℝ
  sY : ι → ℝ
  pd : ι → ℝ
  prep : ∀ i, PrepAt β γ G n N E (μ i) (ν i) (sX i) (sY i) (pd i)
  μ_supp : ∀ i, (μ i).SupportedIn X
  ν_supp : ∀ i, (ν i).SupportedIn Y

attribute [instance] Menu4.fin

/-- Hypothesis (ii) of L4.1 in colour `G` (04:13): no pair at doubled widths on `X × Y` has `G`-density at most
`exp(-n^h)` (equivalently, defect at most `exp(-n^h)` in colour `!G`). -/
def NoPure (β γ : ℝ) (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X Y : Finset (Fin N)) : Prop :=
  ∀ μ' ν' : Law N,
    μ'.WidthLE (2 * (n : ℝ) ^ β) → ν'.WidthLE (2 * (n : ℝ) ^ γ) →
    dens E G μ' ν' ≤ Real.exp (-(n : ℝ) ^ h4 β γ) →
    ¬ (μ'.SupportedIn X ∧ ν'.SupportedIn Y)

/-- A balanced mixture of the menu (04:85–87): both pointwise averages are at most `K / N`. -/
def Balanced {ι : Type} [Fintype ι] {N : ℕ} (ρ : FinProb ι) (μ ν : ι → Law N) (K : ℝ) : Prop :=
  (∀ x, ∑ i, ρ.w i * (μ i).w x ≤ K / N) ∧ (∀ y, ∑ i, ρ.w i * (ν i).w y ≤ K / N)

/-! ## Masks (04:181–183) -/

/-- A mask of a law: a subset of its support of mass at least `1/2`. -/
def IsMask {N : ℕ} (μ : Law N) (S : Finset (Fin N)) : Prop :=
  (∀ x ∈ S, μ.w x ≠ 0) ∧ (1 / 2 : ℝ) ≤ ∑ x ∈ S, μ.w x

/-- The finite type of masks of `μ`. -/
abbrev Mask {N : ℕ} (μ : Law N) := {S : Finset (Fin N) // IsMask μ S}

theorem mask_mass_pos {N : ℕ} {μ : Law N} (S : Mask μ) : 0 < ∑ x ∈ S.1, μ.w x := by
  have h := S.2.2
  linarith

/-- `μ^M`: the law conditioned on the mask. -/
noncomputable def maskLaw {N : ℕ} {μ : Law N} (S : Mask μ) : Law N :=
  μ.restrict S.1 (mask_mass_pos S)

/-- The full support is a mask. -/
noncomputable def fullMask {N : ℕ} (μ : Law N) : Mask μ :=
  ⟨Finset.univ.filter fun x => μ.w x ≠ 0,
    ⟨fun x hx => (Finset.mem_filter.mp hx).2, by
      rw [Finset.sum_filter_ne_zero, μ.sum_eq_one]
      norm_num⟩⟩

instance {N : ℕ} (μ : Law N) : Nonempty (Mask μ) := ⟨fullMask μ⟩

/-! ## The preparatory sample space (04:181–190) -/

/-- Center IDs: a location and a level `0..H`. -/
abbrev Loc (β γ : ℝ) (n : ℕ) := CubeVertex n × Fin (topH β γ n + 1)

/-- Position (or activation) bits for all IDs. -/
abbrev Pos (β γ : ℝ) (n : ℕ) := Loc β γ n → Bool

/-- Tie permutations for all site-levels (D3.8). -/
abbrev Ties (β γ : ℝ) (n : ℕ) := (hd β γ n).Ties

/-- A tuple `W_{c,κ}` of `k` first-side labels for every ID `c` and key `κ`. -/
abbrev Tuples (β γ : ℝ) (n N : ℕ) := Loc β γ n × Key β γ n → Fin (tupLen β γ n) → Fin N

section Sample

variable {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
variable (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)

/-- A mask for `μ_{i_κ}` at every pair `(c, κ)`. -/
abbrev XMasks := ∀ ck : Loc β γ n × Key β γ n, Mask (M.μ (tag ck.2))

/-- A mask for `ν_{i_{g(u)}}` at every odd role. -/
abbrev YMasks := ∀ u : OddRole n, Mask (M.ν (tag (key β γ n u.1)))

/-- Masks and tuples. -/
abbrev Aux := (XMasks M tag × YMasks M tag) × Tuples β γ n N

/-- The preparatory sample: `((positions, (masks, tuples)), activations), ties`. -/
abbrev Prep := ((Pos β γ n × Aux M tag) × Pos β γ n) × Ties β γ n

noncomputable instance instFintypeAux : Fintype (Aux M tag) := instFintypeProd _ _

noncomputable instance instFintypePrep : Fintype (Prep M tag) := instFintypeProd _ _

/-- Mask profiles for the pairs `(c, κ)` (04:183–185, 437–488). -/
abbrev XProf := ∀ ck : Loc β γ n × Key β γ n, FinProb (Mask (M.μ (tag ck.2)))

/-- Mask profiles for the odd roles (04:187–188, 449–455). -/
abbrev YProf := ∀ u : OddRole n, FinProb (Mask (M.ν (tag (key β γ n u.1))))

/-- Tuples given the masks: independent, `W_{c,κ}` with `k` i.i.d. entries from `μ_{i_κ}^{M_{c,κ}}`. -/
noncomputable def tupleLaw (xm : XMasks M tag) : FinProb (Tuples β γ n N) :=
  FinProb.pi fun ck => FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw (xm ck)

/-- Masks from the profiles, then tuples given the masks. -/
noncomputable def auxLaw (q : XProf M tag) (q' : YProf M tag) : FinProb (Aux M tag) :=
  FinProb.bind ((FinProb.pi q).prod (FinProb.pi q')) fun ms => tupleLaw M tag ms.1

/-- D4.4: the preparatory law; positions, masks/tuples, activations and ties are independent (04:189–190). -/
noncomputable def prepLaw (q : XProf M tag) (q' : YProf M tag) : FinProb (Prep M tag) :=
  (((hd β γ n).posLaw.prod (auxLaw M tag q q')).prod (hd β γ n).actLaw).prod (hd β γ n).tieLaw

variable {M tag}

/-- Positions of a preparatory sample. -/
def ppos (ω : Prep M tag) : Pos β γ n := ω.1.1.1

/-- Masks and tuples of a preparatory sample. -/
def paux (ω : Prep M tag) : Aux M tag := ω.1.1.2

/-- Activations of a preparatory sample. -/
def pact (ω : Prep M tag) : Pos β γ n := ω.1.2

/-- Ties of a preparatory sample. -/
def pties (ω : Prep M tag) : Ties β γ n := ω.2

/-- The `(c, κ)` masks. -/
def axm (a : Aux M tag) : XMasks M tag := a.1.1

/-- The odd masks. -/
def aym (a : Aux M tag) : YMasks M tag := a.1.2

/-- The tuples. -/
def aW (a : Aux M tag) : Tuples β γ n N := a.2

/-- Replace the tuple `W_{ck}` by `z` (04:365–376). -/
noncomputable def updW (ω : Prep M tag) (ck : Loc β γ n × Key β γ n) (z : Fin (tupLen β γ n) → Fin N) : Prep M tag :=
  (((ppos ω, ((axm (paux ω), aym (paux ω)), Function.update (aW (paux ω)) ck z)), pact ω), pties ω)

end Sample

/-! ## Retained masses and validity (04:206–233) -/

/-- `y` hits every entry of every tuple `W_{c,κ}`, `c ∈ D`, `κ ∈ Z`. -/
def HitsAll {β γ : ℝ} {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (W : Tuples β γ n N)
    (D : Finset (Loc β γ n)) (Z : Finset (Key β γ n)) (y : Fin N) : Prop :=
  ∀ c ∈ D, ∀ κ ∈ Z, ∀ j, Hits E G (W (c, κ) j) y

/-- The same requirements with those of the single tuple `W_{c₀,κ₀}` omitted (04:213–215). -/
def HitsBut {β γ : ℝ} {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (W : Tuples β γ n N)
    (D : Finset (Loc β γ n)) (Z : Finset (Key β γ n)) (c₀ : Loc β γ n) (κ₀ : Key β γ n)
    (y : Fin N) : Prop :=
  ∀ c ∈ D, ∀ κ ∈ Z, (c, κ) ≠ (c₀, κ₀) → ∀ j, Hits E G (W (c, κ) j) y

/-- The ratio thresholds of validity (04:221–227): `exp(k(-log 2 + c₁ a_*))` for the own key `g(u)`,
`exp(-Lk)` otherwise. -/
noncomputable def ratioThr (β γ : ℝ) {n : ℕ} (u : OddRole n) (κ : Key β γ n) : ℝ :=
  if κ = key β γ n u.1 then Real.exp ((tupLen β γ n : ℝ) * (-Real.log 2 + c1 * aStar β γ n))
  else Real.exp (-(capL β γ n * (tupLen β γ n : ℝ)))

section Validity

variable {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
variable (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)

/-- D4.5: validity of an ID set `D` at the odd role `u` (04:216–227), with `R_u(D)` the masked second law's mass
of `HitsAll`; the ratio conditions are written multiplicatively (the mass condition makes the denominators
positive). -/
structure Valid (u : OddRole n) (a : Aux M tag) (D : Finset (Loc β γ n)) : Prop where
  card_pos : 1 ≤ D.card
  card_le : D.card ≤ setBd β γ n
  mass : Real.exp (-(capL β γ n * (tupLen β γ n : ℝ) * (D.card : ℝ) * ((Zset β γ u).card : ℝ))) ≤
    (maskLaw (aym a u)).pr (HitsAll E G (aW a) D (Zset β γ u))
  ratio : ∀ c ∈ D, ∀ κ ∈ Zset β γ u,
    ratioThr β γ u κ * (maskLaw (aym a u)).pr (HitsBut E G (aW a) D (Zset β γ u) c κ) ≤
      (maskLaw (aym a u)).pr (HitsAll E G (aW a) D (Zset β γ u))

/-! ## Marking and eligibility (04:300–309) -/

/-- The IDs that can be selected around `u` at the level pair `(j, j+1)`: present, at one of the two levels, in
the radius-`r` ball of an even neighbour of `u`. -/
noncomputable def pool (P : Pos β γ n) (u : OddRole n) (j : Fin (topH β γ n)) : Finset (Loc β γ n) :=
  Finset.univ.filter fun c => P c = true ∧ (c.2.val = j.val ∨ c.2.val = j.val + 1) ∧
    ∃ v ∈ oddAdj u, _root_.hammingDist c.1 v ≤ radius β γ n

/-- Candidate ID sets: subsets of the pool of size between `1` and `T`. -/
noncomputable def cands (P : Pos β γ n) (u : OddRole n) (j : Fin (topH β γ n)) :
    Finset (Finset (Loc β γ n)) :=
  (pool P u j).powerset.filter fun D => 1 ≤ D.card ∧ D.card ≤ setBd β γ n

/-- One greedy step: keep `D` if it is disjoint from every kept set. -/
noncomputable def greedyStep {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (D : Finset α) :
    Finset (Finset α) :=
  if ∀ A ∈ F, Disjoint A D then insert D F else F

/-- The greedy maximal disjoint family of a list of sets (a fixed local rule, 04:304–305). -/
noncomputable def greedy {α : Type*} [DecidableEq α] (L : List (Finset α)) : Finset (Finset α) :=
  L.foldl greedyStep ∅

/-- The marked family at `u` and the level pair `(j, j+1)`: a maximal disjoint family of invalid candidates. -/
noncomputable def marked (P : Pos β γ n) (a : Aux M tag) (u : OddRole n) (j : Fin (topH β γ n)) :
    Finset (Finset (Loc β γ n)) :=
  greedy ((cands P u j).filter fun D => ¬ Valid M tag u a D).toList

/-- IDs forbidden at the site `v` and level `l`: marked by an odd neighbour of `v`, at their own level. -/
noncomputable def forbidden (P : Pos β γ n) (a : Aux M tag) (v : CubeVertex n)
    (l : Fin (topH β γ n + 1)) : Finset (Loc β γ n) :=
  Finset.univ.filter fun c => c.2 = l ∧
    ∃ u : OddRole n, v ∈ oddAdj u ∧ ∃ j, ∃ D ∈ marked M tag P a u j, c ∈ D

/-- D4.5: eligibility `E v l` = present IDs at level `l` in the radius-`r` ball of `v`, minus forbidden ones.
It is a function of positions, masks and tuples only, so L3.8 applies with `Aux = masks × tuples`. -/
noncomputable def elig (P : Pos β γ n) (a : Aux M tag) : (hd β γ n).EligMap := fun v l =>
  (Finset.univ.filter fun c : Loc β γ n =>
      P c = true ∧ c.2 = l ∧ _root_.hammingDist c.1 v ≤ radius β γ n) \
    forbidden M tag P a v l

/-- The number of present IDs at level `l` in the radius-`r` ball of `v` (as in L3.8j). -/
noncomputable def countAt (P : Pos β γ n) (v : CubeVertex n) (l : Fin (topH β γ n + 1)) : ℕ :=
  (Finset.univ.filter fun u : CubeVertex n => P (u, l) = true ∧ _root_.hammingDist u v ≤ radius β γ n).card

end Validity

/-! ## Selection, odd rows and even rows (04:329–432) -/

section Rows

variable {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
variable (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)

/-- The selection of the long local height rule with uniform eligible active choices (04:329–331). -/
noncomputable def sel (ω : Prep M tag) (v : CubeVertex n) : Option (Loc β γ n) :=
  (hd β γ n).selection (evenSites n) (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω)) (pties ω) v

/-- The IDs selected by the even neighbours of `u`. -/
noncomputable def selSet (ω : Prep M tag) (u : OddRole n) : Finset (Loc β γ n) :=
  (oddAdj u).biUnion fun v => (sel M tag ω v).toFinset

/-- The odd kernel at `u` is valid: all neighbours select, and their ID set is valid (04:340–343). -/
def OddOK (ω : Prep M tag) (u : OddRole n) : Prop :=
  (∀ v ∈ oddAdj u, sel M tag ω v ≠ none) ∧ Valid M tag u (paux ω) (selSet M tag ω u)

theorem oddOK_mass_pos {ω : Prep M tag} {u : OddRole n} (h : OddOK M tag ω u) :
    0 < (maskLaw (aym (paux ω) u)).pr (HitsAll E G (aW (paux ω)) (selSet M tag ω u) (Zset β γ u)) :=
  lt_of_lt_of_le (Real.exp_pos _) h.2.mass

/-- The sampling law at `u`: the masked second law restricted to the tuple hits and normalized on a valid
kernel; the fixed fallback `ν_{i_{g(u)}}` otherwise (04:343–345). -/
noncomputable def oddDraw (ω : Prep M tag) (u : OddRole n) : Law N :=
  if h : OddOK M tag ω u then
    (maskLaw (aym (paux ω) u)).cond (HitsAll E G (aW (paux ω)) (selSet M tag ω u) (Zset β γ u))
      (oddOK_mass_pos M tag h)
  else M.ν (tag (key β γ n u.1))

/-- D4.6: the odd row `p_u`, a subprobability: the sampling law on a valid kernel, zero otherwise
(04:340–345). -/
noncomputable def oddRow (ω : Prep M tag) (u : OddRole n) (y : Fin N) : ℝ :=
  if OddOK M tag ω u then (oddDraw M tag ω u).w y else 0

/-- D4.6: the local event `E` at the even role `a` with reference `c` (04:355–362): `c` is selected at `a`
by the long rule (so present, eligible, at a good height below `H`); eligibility sizes are legal on `a`'s
consultation ball; all neighbouring odd kernels are valid; prospective counts in every neighbouring-filter
ball, at all levels, are at most `2λ`. -/
structure EvLocal (ω : Prep M tag) (a : EvenRole n) (c : Loc β γ n) : Prop where
  sel_eq : sel M tag ω a.1 = some c
  legal : ∀ v ∈ (hd β γ n).domBall (evenSites n) a.1 (hd β γ n).Rlong, ∀ l,
    (hd β γ n).LegalAt (ppos ω) (elig M tag (ppos ω) (paux ω)) v l
  odd_ok : ∀ j : Fin n, OddOK M tag ω (oddNbr a j)
  counts : ∀ j : Fin n, ∀ v ∈ oddAdj (oddNbr a j), ∀ l, (countAt (ppos ω) v l : ℝ) ≤ 2 * lamH n

/-- The prior of the tuple `W_{c,κ}`: `k` i.i.d. draws from the masked first law (04:366–367). -/
noncomputable def prior (ω : Prep M tag) (c : Loc β γ n) (κ : Key β γ n) :
    FinProb (Fin (tupLen β γ n) → Fin N) :=
  FinProb.pi fun _ => maskLaw (axm (paux ω) (c, κ))

/-- `F_z(y) = 1_E ∏_{u∼a} p_u(y_u)` with the tuple `W_{c,g(a)}` replaced by `z` and every rule recomputed
(04:368–376). -/
noncomputable def lik (ω : Prep M tag) (a : EvenRole n) (c : Loc β γ n)
    (z : Fin (tupLen β γ n) → Fin N) (y : Fin n → Fin N) : ℝ :=
  (if EvLocal M tag (updW ω (c, key β γ n a.1) z) a c then 1 else 0) *
    ∏ j, oddRow M tag (updW ω (c, key β γ n a.1) z) (oddNbr a j) (y j)

/-- `M_c(y) = ∫ F_z(y) dπ(z)` (04:371). -/
noncomputable def marg (ω : Prep M tag) (a : EvenRole n) (c : Loc β γ n) (y : Fin n → Fin N) : ℝ :=
  ∑ z, (prior M tag ω c (key β γ n a.1)).w z * lik M tag ω a c z y

/-- The ID pool of the reference mixture at `u`: present IDs in the radius-`r` balls of the neighbours of `u`, at
all levels (04:379–381). -/
noncomputable def refPool (P : Pos β γ n) (u : OddRole n) : Finset (Loc β γ n) :=
  Finset.univ.filter fun c => P c = true ∧ ∃ v ∈ oddAdj u, _root_.hammingDist c.1 v ≤ radius β γ n

/-- ID sets of size at most `T` containing `c` drawn from the pool (04:379–381). -/
noncomputable def refSets (P : Pos β γ n) (u : OddRole n) (c : Loc β γ n) : Finset (Finset (Loc β γ n)) :=
  (refPool P u).powerset.filter fun D => c ∈ D ∧ D.card ≤ setBd β γ n

/-- One mixture term: the masked second law filtered by all tuples of `D × Z_u` except `W_{c,κ}`, normalized;
the masked law itself when the mass is zero (04:385–388). -/
noncomputable def delLaw (ω : Prep M tag) (u : OddRole n) (D : Finset (Loc β γ n)) (c : Loc β γ n)
    (κ : Key β γ n) : Law N :=
  if h : 0 < (maskLaw (aym (paux ω) u)).pr (HitsBut E G (aW (paux ω)) D (Zset β γ u) c κ) then
    (maskLaw (aym (paux ω) u)).cond (HitsBut E G (aW (paux ω)) D (Zset β γ u) c κ) h
  else maskLaw (aym (paux ω) u)

/-- The count condition and a nonempty family for the reference mixture (04:381–385). -/
def RefOK (ω : Prep M tag) (u : OddRole n) (c : Loc β γ n) : Prop :=
  (∀ v ∈ oddAdj u, ∀ l, (countAt (ppos ω) v l : ℝ) ≤ 2 * lamH n) ∧ (refSets (ppos ω) u c).Nonempty

/-- The reference law `Q_u`: the uniform mixture of the deleted-tuple laws, or the fixed reference `ν_{i_{g(u)}}`
when the count condition fails or the family is empty (04:378–389). -/
noncomputable def refRow (ω : Prep M tag) (u : OddRole n) (c : Loc β γ n) (κ : Key β γ n) : Law N :=
  if h : RefOK M tag ω u c then
    Law.mix (FinProb.uniform (refSets (ppos ω) u c) h.2) fun D => delLaw M tag ω u D c κ
  else M.ν (tag (key β γ n u.1))

/-- `Q(y) = ∏_{u∼a} Q_u(y_u)` (04:390). -/
noncomputable def refProd (ω : Prep M tag) (a : EvenRole n) (c : Loc β γ n) (y : Fin n → Fin N) : ℝ :=
  ∏ j, (refRow M tag ω (oddNbr a j) c (key β γ n a.1)).w (y j)

/-- The predictive requirement `M_c > 0`, `M_c ≥ ε₄ Q` (04:409–411). -/
def PredOK (ω : Prep M tag) (a : EvenRole n) (c : Loc β γ n) (y : Fin n → Fin N) : Prop :=
  0 < marg M tag ω a c y ∧ eps4 β γ n * refProd M tag ω a c y ≤ marg M tag ω a c y

/-- `S_{a,c}(y)`: the common `G`-neighbours of the odd labels inside the mask `M_{c,g(a)}` (04:197–200). -/
noncomputable def comm (ω : Prep M tag) (a : EvenRole n) (c : Loc β γ n) (y : Fin n → Fin N) :
    Finset (Fin N) :=
  (axm (paux ω) (c, key β γ n a.1)).1.filter fun x => ∀ j, Hits E G x (y j)

/-- D4.6: the even row `p_a` at odd-neighbour labels `y`: uniform on `S_{a,c}(y)` when the selected reference
`c` meets `E` and the predictive requirement, zero otherwise (04:428–432). -/
noncomputable def evenRowAt (ω : Prep M tag) (a : EvenRole n) (y : Fin n → Fin N) (x : Fin N) : ℝ :=
  (sel M tag ω a.1).elim 0 fun c =>
    if EvLocal M tag ω a c ∧ PredOK M tag ω a c y ∧ x ∈ comm M tag ω a c y then
      ((comm M tag ω a c y).card : ℝ)⁻¹ else 0

end Rows

/-! ## Events, column sums and raw rows (04:300–338, 437–597) -/

section Events

variable {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
variable (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)

/-- Predictive failure at `a`: the selected reference fails `M_c > 0 ∧ M_c ≥ ε₄ Q` (04:531–532). -/
def PredFail (ω : Prep M tag) (a : EvenRole n) (y : Fin n → Fin N) : Prop :=
  ∃ c, sel M tag ω a.1 = some c ∧ ¬ PredOK M tag ω a c y

/-- Geometric success (04:311–338): every site-level ball has between `λ/2` and `2λ` present IDs; every marked
family has fewer than `n` members; the long rule has good heights for the eligibility `elig`. -/
structure GeoSucc (ω : Prep M tag) : Prop where
  counts : ∀ v l, lamH n / 2 ≤ (countAt (ppos ω) v l : ℝ) ∧ (countAt (ppos ω) v l : ℝ) ≤ 2 * lamH n
  families : ∀ (u : OddRole n) j, (marked M tag (ppos ω) (paux ω) u j).card < n
  heights : (hd β γ n).GoodHeights (evenSites n) (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω))

/-- The odd column sum at a second-side label. -/
noncomputable def oddCol (ω : Prep M tag) (y : Fin N) : ℝ := ∑ u : OddRole n, oddRow M tag ω u y

/-- `S_pre` (04:510–512): geometric success and odd column sums at most `1/10`. -/
def SPre (ω : Prep M tag) : Prop := GeoSucc M tag ω ∧ ∀ y, oddCol M tag ω y ≤ 1 / 10

/-- The odd injection law at a history (04:512–526, Lemma 3.9): injective labels, and joint probabilities of at
most `n²` specified odd outputs at most twice the product of the odd rows. -/
def InjOK (ω : Prep M tag) (J : FinProb (OddRole n → Fin N)) : Prop :=
  (∀ f, J.w f ≠ 0 → Function.Injective f) ∧
    ∀ (S : Finset (OddRole n)) (o : OddRole n → Fin N), (S.card : ℝ) ≤ (n : ℝ) ^ 2 →
      J.pr (fun f => ∀ u ∈ S, f u = o u) ≤ 2 * ∏ u ∈ S, oddRow M tag ω u (o u)

/-- The even column sum at a first-side label. -/
noncomputable def evenCol (ω : Prep M tag) (f : OddRole n → Fin N) (x : Fin N) : ℝ :=
  ∑ a : EvenRole n, evenRowAt M tag ω a (nbrLabels f a) x

/-- Independent odd draws from the sampling laws (the raw experiment, 04:438–440). -/
noncomputable def oddDrawLaw (ω : Prep M tag) : FinProb (OddRole n → Fin N) :=
  FinProb.pi (oddDraw M tag ω)

/-- The mean even row at a history under independent odd draws. -/
noncomputable def evenMean (ω : Prep M tag) (a : EvenRole n) (x : Fin N) : ℝ :=
  (oddDrawLaw M tag ω).expect fun f => evenRowAt M tag ω a (nbrLabels f a) x

/-- `E_raw p_u(y)` (04:442–443). -/
noncomputable def rawOdd (q : XProf M tag) (q' : YProf M tag) (u : OddRole n) (y : Fin N) : ℝ :=
  (prepLaw M tag q q').expect fun ω => oddRow M tag ω u y

/-- `E_raw p_a(x)` (04:444–445). -/
noncomputable def rawEven (q : XProf M tag) (q' : YProf M tag) (a : EvenRole n) (x : Fin N) : ℝ :=
  (prepLaw M tag q q').expect fun ω => evenMean M tag ω a x

/-- `ω` and `ω'` agree on every coordinate located in `S`: positions, activations and ties of IDs (site-levels)
located in `S`, masks and tuples of pairs `(c, κ)` with `c` located in `S`, odd masks of odd roles in `S`. -/
def AgreeOn (S : Finset (CubeVertex n)) (ω ω' : Prep M tag) : Prop :=
  (∀ c : Loc β γ n, c.1 ∈ S →
      ppos ω c = ppos ω' c ∧ pact ω c = pact ω' c ∧ pties ω c = pties ω' c) ∧
    (∀ ck : Loc β γ n × Key β γ n, ck.1.1 ∈ S →
      axm (paux ω) ck = axm (paux ω') ck ∧ aW (paux ω) ck = aW (paux ω') ck) ∧
    (∀ u : OddRole n, u.1 ∈ S → aym (paux ω) u = aym (paux ω') u)

/-- `f` reads only coordinates located in `S`. -/
def LocalTo (S : Finset (CubeVertex n)) (f : Prep M tag → ℝ) : Prop :=
  ∀ ω ω', AgreeOn M tag S ω ω' → f ω = f ω'

end Events

/-- The locality radius `R_long + r + 4` of the rows. -/
noncomputable def locR (β γ : ℝ) (n : ℕ) : ℕ := (hd β γ n).Rlong + radius β γ n + 4

/-- Pairwise separation by more than `2 locR` (so radius-`locR` balls are disjoint). -/
def Sep (β γ : ℝ) {n m : ℕ} (s : Fin m → CubeVertex n) : Prop :=
  ∀ i j, i ≠ j → 2 * locR β γ n < _root_.hammingDist (s i) (s j)

/-- The selection-probability weight `w_c` (04:463–474): `(λ/V)(3/λ) = 3/V` at level zero,
`(λ/V) exp(-n^{c₃})` above. -/
noncomputable def wc (β γ : ℝ) (n : ℕ) (c₃ : ℝ) (c : Loc β γ n) : ℝ :=
  if c.2.val = 0 then 3 / ((hd β γ n).V : ℝ)
  else lamH n / ((hd β γ n).V : ℝ) * Real.exp (-(n : ℝ) ^ c₃)

/-! ## Named facts (the conclusions of the nodes) -/

section Facts

/-- L4.1c(1): `|Z_u| ≤ n^{γ - 0.9ω}`. -/
def KeyNbrCard (β γ : ℝ) (n : ℕ) : Prop :=
  ∀ u : OddRole n, ((Zset β γ u).card : ℝ) ≤ (n : ℝ) ^ (γ - 9 / 10 * omega4 β γ)

/-- L4.1c(3): at most `n^{γ+14ω}` coordinate flips change the key. -/
def KeyLocal (β γ : ℝ) (n : ℕ) : Prop :=
  ∀ v : CubeVertex n,
    ((Finset.univ.filter fun j => key β γ n (cubeFlip v j) ≠ key β γ n v).card : ℝ) ≤
      (n : ℝ) ^ (γ + 14 * omega4 β γ)

/-- L4.1c(2): every key has mass at most `exp(-n^{γ+ω}/10)` on either parity class. -/
def KeyFiber (β γ : ℝ) (n : ℕ) : Prop :=
  ∀ κ : Key β γ n,
    ((Finset.univ.filter fun a : EvenRole n => key β γ n a.1 = κ).card : ℝ) ≤
        Real.exp (-(n : ℝ) ^ (γ + omega4 β γ) / 10) * Fintype.card (EvenRole n) ∧
      ((Finset.univ.filter fun u : OddRole n => key β γ n u.1 = κ).card : ℝ) ≤
        Real.exp (-(n : ℝ) ^ (γ + omega4 β γ) / 10) * Fintype.card (OddRole n)

variable {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
variable (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)

/-- L4.1d: bounded normalized parity averages of the tagged patch laws (04:145–147). -/
def TagBal (K : ℝ) : Prop :=
  (∀ x, (Fintype.card (EvenRole n) : ℝ)⁻¹ *
      ∑ a : EvenRole n, (N : ℝ) * (M.μ (tag (key β γ n a.1))).w x ≤ K) ∧
    ∀ y, (Fintype.card (OddRole n) : ℝ)⁻¹ *
      ∑ u : OddRole n, (N : ℝ) * (M.ν (tag (key β γ n u.1))).w y ≤ K

/-- L4.1e1 (low entries, 04:245–252): an entry from a masked first law retains less than `e^{-L}` of a law on
`Y` of width at most `2n^γ` with probability at most `exp(-n^{β-ω/2}/4)`. -/
def EntryLow : Prop :=
  ∀ i (S : Mask (M.μ i)) (η : Law N), η.SupportedIn Y → η.WidthLE (2 * (n : ℝ) ^ γ) →
    (maskLaw S).pr (fun x => rowDeg E G x η < Real.exp (-capL β γ n)) ≤
      Real.exp (-(n : ℝ) ^ (β - omega4 β γ / 2) / 4)

/-- L4.1e1 (own key, 04:254–281): for a law on the support of `ν_i` within the second width margin, an entry from
a masked `μ_i` dips below `p - a_i/4` with probability at most `20 n^{-ω/5}/a_i`. -/
def EntryOwn : Prop :=
  ∀ i (S : Mask (M.μ i)) (η : Law N), (∀ y, (M.ν i).w y = 0 → η.w y = 0) →
    η.WidthLE (M.sY i + (n : ℝ) ^ (γ - omega4 β γ / 2) / 4) →
    (maskLaw S).pr (fun x => rowDeg E G x η < M.pd i - (M.pd i - 1 / 2) / 4) ≤
      20 * (n : ℝ) ^ (-(omega4 β γ) / 5) / (M.pd i - 1 / 2)

/-- The low part of validity failure: the mass condition fails, or a cross-key ratio fails. -/
def LowFail (ym : YMasks M tag) (u : OddRole n) (D : Finset (Loc β γ n))
    (W : Tuples β γ n N) : Prop :=
  (maskLaw (ym u)).pr (HitsAll E G W D (Zset β γ u)) <
      Real.exp (-(capL β γ n * (tupLen β γ n : ℝ) * (D.card : ℝ) * ((Zset β γ u).card : ℝ))) ∨
    ∃ c ∈ D, ∃ κ ∈ Zset β γ u, κ ≠ key β γ n u.1 ∧
      (maskLaw (ym u)).pr (HitsAll E G W D (Zset β γ u)) <
        ratioThr β γ u κ * (maskLaw (ym u)).pr (HitsBut E G W D (Zset β γ u) c κ)

/-- L4.1e2 (low): `Pr(LowFail) ≤ exp(-2n^{ω/5})` for fixed masks. -/
def ExposureLow : Prop :=
  ∀ (xm : XMasks M tag) (ym : YMasks M tag) (u : OddRole n) (D : Finset (Loc β γ n)),
    1 ≤ D.card → D.card ≤ setBd β γ n →
    (tupleLaw M tag xm).pr (LowFail M tag ym u D) ≤ Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5))

/-- L4.1e2 (own key): the own-key ratio at `(c, g(u))` fails with probability at most `exp(-2n^{ω/5})`. -/
def OwnRatio : Prop :=
  ∀ (xm : XMasks M tag) (ym : YMasks M tag) (u : OddRole n) (D : Finset (Loc β γ n)) (c : Loc β γ n),
    1 ≤ D.card → D.card ≤ setBd β γ n → c ∈ D → key β γ n u.1 ∈ Zset β γ u →
    (tupleLaw M tag xm).pr (fun W =>
        (maskLaw (ym u)).pr (HitsAll E G W D (Zset β γ u)) <
          ratioThr β γ u (key β γ n u.1) *
            (maskLaw (ym u)).pr (HitsBut E G W D (Zset β γ u) c (key β γ n u.1))) ≤
      Real.exp (-2 * (n : ℝ) ^ (omega4 β γ / 5))

/-- L4.1e: for fixed masks, a fixed ID set of size in `[1, T]` is invalid with probability at most
`exp(-n^{ω/5})` (04:235–236). -/
def ValidProb : Prop :=
  ∀ (xm : XMasks M tag) (ym : YMasks M tag) (u : OddRole n) (D : Finset (Loc β γ n)),
    1 ≤ D.card → D.card ≤ setBd β γ n →
    (tupleLaw M tag xm).pr (fun W => ¬ Valid M tag u ((xm, ym), W) D) ≤
      Real.exp (-(n : ℝ) ^ (omega4 β γ / 5))

/-- L4.1f (eligibility): lower counts and small families give legal eligibility on the even sites. -/
def LegalOf : Prop :=
  ∀ ω : Prep M tag, (∀ v l, lamH n / 2 ≤ (countAt (ppos ω) v l : ℝ)) →
    (∀ (u : OddRole n) j, (marked M tag (ppos ω) (paux ω) u j).card < n) →
    (hd β γ n).Legal (ppos ω) (elig M tag (ppos ω) (paux ω)) (evenSites n)

/-- L4.1f (selection): good heights give a selection at every even site. -/
def SelectOf : Prop :=
  ∀ ω : Prep M tag,
    (hd β γ n).GoodHeights (evenSites n) (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω)) →
    ∀ a : EvenRole n, sel M tag ω a.1 ≠ none

/-- L4.1f (marking): good heights make every odd kernel valid. -/
def OddOKOf : Prop :=
  ∀ ω : Prep M tag,
    (hd β γ n).GoodHeights (evenSites n) (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω)) →
    ∀ u : OddRole n, OddOK M tag ω u

/-- L4.1f: the deterministic consequences of geometric success (04:329–338). -/
def GeoCons : Prop :=
  ∀ ω : Prep M tag, GeoSucc M tag ω → (∀ a : EvenRole n, ∃ c, EvLocal M tag ω a c) ∧
    ∀ u : OddRole n, OddOK M tag ω u

/-- D4.6: the odd-row cap `N p_u(y) ≤ exp(2n^γ)` (04:349–351). -/
def OddCap : Prop :=
  ∀ (ω : Prep M tag) (u : OddRole n) (y : Fin N), (N : ℝ) * oddRow M tag ω u y ≤ Real.exp (2 * (n : ℝ) ^ γ)

/-- L4.1g(1): the reference product and the marginal do not read the tuple `W_{c,g(a)}` (04:386–389). -/
def RefIndep : Prop :=
  ∀ (ω : Prep M tag) (a : EvenRole n) (c : Loc β γ n) (z : Fin (tupLen β γ n) → Fin N)
    (y : Fin n → Fin N),
    refProd M tag (updW ω (c, key β γ n a.1) z) a c y = refProd M tag ω a c y ∧
      marg M tag (updW ω (c, key β γ n a.1) z) a c y = marg M tag ω a c y

/-- L4.1g(2): `F_z(y) ≤ exp((log 2 - c₂ a_*) k n) Q(y)` (04:392–404). -/
def LikBound : Prop :=
  ∀ (ω : Prep M tag) (a : EvenRole n) (c : Loc β γ n) (z : Fin (tupLen β γ n) → Fin N)
    (y : Fin n → Fin N),
    lik M tag ω a c z y ≤
      Real.exp ((Real.log 2 - c2 * aStar β γ n) * (tupLen β γ n : ℝ) * (n : ℝ)) * refProd M tag ω a c y

/-- L4.1g(3): on the predictive requirement, `|S| ≥ N exp(-(log 2 - c₂ a_*/2) n)` (04:409–427). -/
def CommLarge : Prop :=
  ∀ (ω : Prep M tag) (a : EvenRole n) (c : Loc β γ n) (y : Fin n → Fin N), PredOK M tag ω a c y →
    (N : ℝ) * Real.exp (-((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ))) ≤ (comm M tag ω a c y).card

/-- L4.1g: the even rows are subprobabilities supported in the mask of the selected reference on common
`G`-neighbours, probabilities on `E` and the predictive requirement, with cap
`N p_a ≤ exp((log 2 - c₂ a_*/2) n)` (04:428–432, 556–557). -/
def EvenRowFacts : Prop :=
  ∀ (ω : Prep M tag) (a : EvenRole n) (y : Fin n → Fin N),
    (∀ x, 0 ≤ evenRowAt M tag ω a y x) ∧
    (∑ x, evenRowAt M tag ω a y x ≤ 1) ∧
    (∀ c, EvLocal M tag ω a c → PredOK M tag ω a c y → ∑ x, evenRowAt M tag ω a y x = 1) ∧
    (∀ x, evenRowAt M tag ω a y x ≠ 0 → (∀ j, Hits E G x (y j)) ∧
      ∃ c, sel M tag ω a.1 = some c ∧ EvLocal M tag ω a c ∧ x ∈ (axm (paux ω) (c, key β γ n a.1)).1) ∧
    (∀ x, (N : ℝ) * evenRowAt M tag ω a y x ≤
      Real.exp ((Real.log 2 - c2 * aStar β γ n / 2) * (n : ℝ)))

/-- L4.1h (selection probability, 04:469–477): `Pr(E at a with reference c) ≤ w_c` for all mask profiles. -/
def SelectBound (c₃ : ℝ) : Prop :=
  ∀ (q : XProf M tag) (q' : YProf M tag) (a : EvenRole n) (c : Loc β γ n),
    (prepLaw M tag q q').pr (fun ω => EvLocal M tag ω a c) ≤ wc β γ n c₃ c

/-- L4.1h: mask profiles balancing the raw rows (04:441–447). -/
structure ProfOK (q : XProf M tag) (q' : YProf M tag) : Prop where
  odd : ∀ u y, rawOdd M tag q q' u y ≤ 2 * (M.ν (tag (key β γ n u.1))).w y
  even : ∀ x, ∑ a : EvenRole n, rawEven M tag q q' a x ≤
    8 * ∑ a : EvenRole n, (M.μ (tag (key β γ n a.1))).w x

/-- Locality of eligibility: radius `r + 2`. -/
def EligLocal : Prop :=
  ∀ (v : CubeVertex n) (l : Fin (topH β γ n + 1)) (ω ω' : Prep M tag),
    AgreeOn M tag (ballV v (radius β γ n + 2)) ω ω' →
    elig M tag (ppos ω) (paux ω) v l = elig M tag (ppos ω') (paux ω') v l

/-- Locality of the selection: radius `R_long + r + 2`. -/
def SelLocal : Prop :=
  ∀ (v : CubeVertex n) (ω ω' : Prep M tag),
    AgreeOn M tag (ballV v ((hd β γ n).Rlong + radius β γ n + 2)) ω ω' → sel M tag ω v = sel M tag ω' v

/-- Locality of the odd kernels: radius `R_long + r + 3`. -/
def OddLocal : Prop :=
  ∀ (u : OddRole n) (ω ω' : Prep M tag),
    AgreeOn M tag (ballV u.1 ((hd β γ n).Rlong + radius β γ n + 3)) ω ω' →
    (OddOK M tag ω u ↔ OddOK M tag ω' u) ∧ ∀ y, (oddDraw M tag ω u).w y = (oddDraw M tag ω' u).w y

/-- Locality of the mean even rows: radius `locR = R_long + r + 4`. -/
def EvenLocal : Prop :=
  ∀ (a : EvenRole n) (x : Fin N), LocalTo M tag (ballV a.1 (locR β γ n)) fun ω => evenMean M tag ω a x

/-- Independence of local functions on disjoint location sets under the preparatory law. -/
def PrepFactor (q : XProf M tag) (q' : YProf M tag) : Prop :=
  ∀ (m : ℕ) (S : Fin m → Finset (CubeVertex n)) (f : Fin m → Prep M tag → ℝ),
    (∀ i j, i ≠ j → Disjoint (S i) (S j)) → (∀ i, LocalTo M tag (S i) (f i)) →
    (prepLaw M tag q q').expect (fun ω => ∏ i, f i ω) = ∏ i, (prepLaw M tag q q').expect (f i)

/-- Resampling one tuple from its prior leaves the preparatory law invariant (04:536–539). -/
def Resample (q : XProf M tag) (q' : YProf M tag) : Prop :=
  ∀ (c : Loc β γ n) (κ : Key β γ n) (g : Prep M tag → ℝ),
    (prepLaw M tag q q').expect g =
      (prepLaw M tag q q').expect fun ω => ∑ z, (prior M tag ω c κ).w z * g (updW ω (c, κ) z)

/-- Separated odd products in the raw experiment factor (04:500–502). -/
def OddFactor (q : XProf M tag) (q' : YProf M tag) : Prop :=
  ∀ (y : Fin N) (m : ℕ) (u : Fin m → OddRole n), Sep β γ (fun i => (u i).1) →
    (prepLaw M tag q q').expect (fun ω => ∏ i, (N : ℝ) * oddRow M tag ω (u i) y) ≤
      ∏ i, (N : ℝ) * rawOdd M tag q q' (u i) y

/-- Separated even products in the raw experiment factor (04:575–585). -/
def EvenFactor (q : XProf M tag) (q' : YProf M tag) : Prop :=
  ∀ (x : Fin N) (m : ℕ) (a : Fin m → EvenRole n), Sep β γ (fun i => (a i).1) →
    (prepLaw M tag q q').expect (fun ω => ∏ i, (N : ℝ) * evenMean M tag ω (a i) x) ≤
      ∏ i, (N : ℝ) * rawEven M tag q q' (a i) x

/-- L4.1k (comparison step, 04:562–574): at a pre-injection history, separated even products under an injection
law are at most twice their mean under independent odd draws. -/
def EvenClock : Prop :=
  ∀ (ω : Prep M tag) (J : FinProb (OddRole n → Fin N)), SPre M tag ω → InjOK M tag ω J →
    ∀ (x : Fin N) (m : ℕ) (a : Fin m → EvenRole n), m ≤ n → Sep β γ (fun i => (a i).1) →
      J.expect (fun f => ∏ i, (N : ℝ) * evenRowAt M tag ω (a i) (nbrLabels f (a i)) x) ≤
        2 * ∏ i, (N : ℝ) * evenMean M tag ω (a i) x

end Facts

end HypercubeRamsey.S04
