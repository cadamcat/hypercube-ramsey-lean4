import HypercubeRamsey.S05.History
import HypercubeRamsey.S05.Selection
import HypercubeRamsey.S03.Height.Selection
import HypercubeRamsey.S05.Centres_sol_s05_g1
import HypercubeRamsey.S05.Centres_sol_s05_centres_scales
import HypercubeRamsey.S05.Centres_sol_s05_centres_records
import HypercubeRamsey.S05.Centres_sol_s05_centres_height
import HypercubeRamsey.S05.Centres_sol_s05_centres_low
import HypercubeRamsey.S05.Centres_sol_s05_centres_counts
import HypercubeRamsey.S05.Centres_sol_s05_j5_stars

/-!
# D5.6–D5.8, L5.1j, L5.1g/k rows, L5.1l(3): centers, height choices and the odd rows

At a key history the center experiment is a product over ambient locations of presence, activation, a tie
permutation and an array of every type (05:177–187, 05:315–325).  The long and short height rules of the
device D3.8 select one center ID per even state from the pre-activation eligible sets (05:818–894).  The odd
rows are attached to odd roles: high rows are the common law of L5.1g, low rows the selection-corrected
posteriors of L5.1k (05:896–1001).  All objects are functions of the key history, so that the history-level
estimates of L5.1l(2) can average over hidden keys.
-/

namespace HypercubeRamsey

open Classical OAI.HypercubeRamsey

set_option synthInstance.maxSize 4096

noncomputable section

variable {γ K' χ : ℝ}

namespace Setup5

variable {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} (X : Setup5 γ K' χ n N E G)

/-! ### The height device at this dimension (05:315–329) -/

/-- The height exponents, fixed from `α` before the dimension threshold (05:318–325): admissible for D3.8
with `λ = n^{10}`, `D = 8`, linear radius `r = ⌊ρ n⌋`, `θ > .9` and eventually `2 n^b ≤ T`. -/
structure HeightChoice5 where
  b₀ : ℝ
  b : ℝ
  σ : ℝ
  ζ : ℝ
  θ : ℝ
  a : ℝ
  adm : HDAdmissible 10 b₀ b σ ζ θ a (1 / 2) 2 8
  regime : HDRegime b₀ b 8
  hθ : 9 / 10 < θ
  hbT : b < X.p.alpha / 1000
  /-- One admissible family fixed by `α`, before the eventual dimension threshold (05:318–329).
  In particular the slack exponent has the uniform gap `ζ - σ = 9α/1000000`. -/
  fixed : b₀ = X.p.alpha / 10000 ∧ b = X.p.alpha / 2000 ∧
    σ = X.p.alpha / 1000000 ∧ ζ = X.p.alpha / 100000 ∧
    θ = 1 - X.p.alpha / 100000 ∧ a = X.p.alpha / 20000

variable {X}

/-- The device parameters: sites in the one-hot cube of the states. -/
def HeightChoice5.hp (h : X.HeightChoice5) : HDParams where
  n := n
  d := X.St.d
  D := 8
  r := ⌊X.p.rho * n⌋₊
  H := topScale n h.σ h.ζ
  lam := (n : ℝ) ^ (10 : ℝ)
  b₀ := h.b₀
  b := h.b

variable (X)

/-- What is drawn at one ambient location: presence, activation, tie permutation, and an array of every type. -/
abbrev CVal (h : X.HeightChoice5) := Bool × Bool × h.hp.TiePerm × (∀ K : X.Ty, X.Array K)

/-- The center experiment's sample space. -/
abbrev CΩ (h : X.HeightChoice5) := ∀ l : h.hp.Loc, X.CVal h

noncomputable instance instFintypeCVal (h : X.HeightChoice5) : Fintype (X.CVal h) := inferInstance

noncomputable instance instFintypeCΩ (h : X.HeightChoice5) : Fintype (X.CΩ h) :=
  @Pi.instFintype _ _ inferInstance inferInstance (fun _ => inferInstance)

/-- The center law at a key history: independent presence, activations, ties, and arrays of independent
`P_K`-blocks generated at every ID, present or not (05:181–187, 05:249–254). -/
def centreLaw (h : X.HeightChoice5) (H : X.KeyHist) : FinProb (X.CΩ h) :=
  FinProb.pi fun _ =>
    (FinProb.bernoulli (h.hp.lam / (h.hp.V : ℝ))).prod
      ((FinProb.bernoulli ((n : ℝ) ^ h.b₀ / h.hp.lam)).prod
        ((FinProb.uniformAll (Ω := h.hp.TiePerm) ⟨1⟩).prod
          (FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K)))

variable {X}
variable {h : X.HeightChoice5}

/-- Prospective presence. -/
def pos (ω : X.CΩ h) : h.hp.Loc → Bool := fun l => (ω l).1
/-- Activations. -/
def act (ω : X.CΩ h) : h.hp.Loc → Bool := fun l => (ω l).2.1
/-- Tie permutations. -/
def tie (ω : X.CΩ h) : h.hp.Ties := fun l => (ω l).2.2.1
/-- The array of type `K` at a location. -/
def arr (ω : X.CΩ h) (l : h.hp.Loc) (K : X.Ty) : X.Array K := (ω l).2.2.2 K
/-- All arrays, indexed by (location, type). -/
def arraysOf (ω : X.CΩ h) : X.ArraysOn h.hp.Loc := fun c => arr ω c.1 c.2

variable (X)

/-- Height sites: the one-hot images of the even states (05:315–317). -/
def sites (h : X.HeightChoice5) : h.hp.Sites :=
  Finset.univ.image fun v : EvenRole5 n => X.St.oneHot (X.St.stateOf v.1)

/-- The site of an even role. -/
def siteOf (v : EvenRole5 n) : CubeVertex X.St.d := X.St.oneHot (X.St.stateOf v.1)

/-- Selection with either consultation radius, using the same eligibility and ties (05:861–879). -/
def selAt (elig : X.CΩ h → h.hp.EligMap) (ω : X.CΩ h) (R : ℕ) (v : EvenRole5 n) : Option h.hp.Loc :=
  h.hp.selectionAt (X.sites h) (pos ω) (act ω) (elig ω) (tie ω) R (X.siteOf v)

/-- The long-rule selection at an even role (05:851–853). -/
def selLong (elig : X.CΩ h → h.hp.EligMap) (ω : X.CΩ h) (v : EvenRole5 n) : Option h.hp.Loc :=
  h.hp.selection (X.sites h) (pos ω) (act ω) (elig ω) (tie ω) (X.siteOf v)

/-- The short-rule selection, consultation radius `D ⌊√m⌋` (05:328–329). -/
def selShort (elig : X.CΩ h → h.hp.EligMap) (ω : X.CΩ h) (v : EvenRole5 n) : Option h.hp.Loc :=
  h.hp.selectionAt (X.sites h) (pos ω) (act ω) (elig ω) (tie ω) (h.hp.Rshort (X.p.m n)) (X.siteOf v)

/-- The block subset of the tuple used at even role `v` with array at `l` (05:155–160): the whole low array; at a
high type the first `k_*/u_*` pool blocks hitting the optional column if there are enough, otherwise the first
blocks. -/
def refSubset (H : X.KeyHist) (ω : X.CΩ h) (v : EvenRole5 n) (l : h.hp.Loc) : Finset (Fin X.blockBound) :=
  X.refSubsetOn H (arraysOf ω) (l, X.g.evenType (X.p.J n) v.1) (X.g.optionalKey (X.p.J n) v.1)

/-- A center reference: location and block subset. -/
abbrev CRef (h : X.HeightChoice5) := h.hp.Loc × Finset (Fin X.blockBound)

/-- The reference selected at an even role by the long rule. -/
def evenRefOf (elig : X.CΩ h → h.hp.EligMap) (H : X.KeyHist) (ω : X.CΩ h) (v : EvenRole5 n) :
    Option (X.CRef h) :=
  (X.selLong elig ω v).map fun l => (l, X.refSubset H ω v l)

/-- The record of an odd role at a specified consultation radius (05:331–343,861–879): its neighbours' selected arrays, the needed same-mode
references, and at a low role with a high neighbour, that pool and the mask hit by the actual target. -/
def actualRecordAt (elig : X.CΩ h → h.hp.EligMap) (H : X.KeyHist) (ω : X.CΩ h) (R : ℕ) (y : OddRole5 n) :
    X.RecordOn h.hp.Loc :=
  let ℓ := X.g.roleKey (X.p.J n) y.1
  let obs : Finset (h.hp.Loc × X.Ty) := (evenNbrs y).biUnion fun a =>
    match X.selAt elig ω R a with
    | some l => {(l, X.g.evenType (X.p.J n) a.1)}
    | none => ∅
  let refs : Finset (h.hp.Loc × X.Ty × Option X.Key) := (evenNbrs y).biUnion fun a =>
    match X.selAt elig ω R a with
    | some l =>
      if ℓ ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          ℓ.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome then
        {(l, X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)} else ∅
    | none => ∅
  let mask : Option (h.hp.Loc × X.Ty × Finset (Fin X.blockBound)) :=
    match ℓ with
    | .inl k =>
      if hex : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (X.selAt elig ω R a).isSome then
        let a := Classical.choose hex
        match X.selAt elig ω R a with
        | some l =>
          some (l, X.g.evenType (X.p.J n) a.1,
            X.firstK (X.hitSet (arraysOf ω) (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k))
              (X.p.usedBlocks n))
        | none => none
      else none
    | .inr _ => none
  (ℓ, obs, refs, mask)

/-- The actual long-rule record. -/
def actualRecord (elig : X.CΩ h → h.hp.EligMap) (H : X.KeyHist) (ω : X.CΩ h) (y : OddRole5 n) :
    X.RecordOn h.hp.Loc :=
  X.actualRecordAt elig H ω h.hp.Rlong y

/-- The tuple of a reference: its blocks in the array of the even role's type. -/
def refBlocks (ω : X.CΩ h) (v : EvenRole5 n) (c : X.CRef h) :
    Finset (X.Block (X.g.evenType (X.p.J n) v.1)) :=
  (Finset.univ.filter fun i : Fin (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1)) =>
    ∃ j ∈ c.2, X.blockIdx _ j = some i).image (arr ω c.1 (X.g.evenType (X.p.J n) v.1))

/-- The average coordinate marginal `P̄_K` of a block law (05:787–789). -/
def avgMarg (H : X.KeyHist) (K : X.Ty) (x : Fin N) : ℝ :=
  ((X.p.q0 * X.p.typeSegs n K : ℕ) : ℝ)⁻¹ *
    ∑ z, (X.blockLaw H K).w z * ((Finset.univ.filter fun e : Fin (X.p.typeSegs n K) × Fin X.p.q0 =>
      z e.1 e.2 = x).card : ℝ)

/-- Prior-heavy labels for a type: `N P̄_K(x) > B_K = A_K^{K_B}` (05:789–791). -/
def PriorHeavy (H : X.KeyHist) (K : X.Ty) (x : Fin N) : Prop :=
  X.blockConst K ^ X.p.KB < (N : ℝ) * X.avgMarg H K x

/-- The number of prior-heavy entries in the tuple of a reference. -/
def heavyCount (H : X.KeyHist) (ω : X.CΩ h) (v : EvenRole5 n) (c : X.CRef h) : ℕ :=
  ∑ i : Fin (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1)),
    if ∃ j ∈ c.2, X.blockIdx _ j = some i then
      (Finset.univ.filter fun e : Fin (X.p.typeSegs n (X.g.evenType (X.p.J n) v.1)) × Fin X.p.q0 =>
        X.PriorHeavy H (X.g.evenType (X.p.J n) v.1) (arr ω c.1 (X.g.evenType (X.p.J n) v.1) i e.1 e.2)).card
    else 0

/-- Ambient locations within a radius of a role's state image (all levels): the consultation scope. -/
def scopeBall (x : CubeVertex n) (rad : ℕ) : Finset h.hp.Loc :=
  Finset.univ.filter fun l => hammingDist l.1 (X.St.oneHot (X.St.stateOf x)) ≤ rad

/-! ### L5.1j: eligibility, the two height rules, and geometry success (05:818–894) -/

/-- The center base layer.  `elig` is the pre-activation eligible map after the singleton removals and the
maximal disjoint markings of Step 3 failures (05:822–833); `valid` is local validity at an odd role (05:866–879);
`success` is the global geometry event of 05:835–860. Local validity includes raw support, positive true
posterior paths and local position counts (05:869–879). It reads the center data within ambient radius
`r + slack`; the fixed exponent family makes the slack bound uniformly sublinear. -/
structure CentreLayer5 where
  ht : X.HeightChoice5
  elig : X.KeyHist → X.CΩ ht → ht.hp.EligMap
  elig_preActivation : ∀ H (ω ω' : X.CΩ ht),
    (∀ l, (ω l).1 = (ω' l).1 ∧ (ω l).2.2.2 = (ω' l).2.2.2) → elig H ω = elig H ω'
  elig_shape : ∀ H ω s j l, l ∈ elig H ω s j → pos ω l = true ∧ l.2 = j ∧ hammingDist l.1 s ≤ ht.hp.r
  valid : X.KeyHist → X.CΩ ht → OddRole5 n → Prop
  success : X.KeyHist → X.CΩ ht → Prop
  slack : ℕ
  slack_small : (slack : ℝ) ≤ (n : ℝ) ^ (1 - (ht.ζ - ht.σ) / 4)
  slack_large : ht.hp.Rlong + 32 ≤ slack
  /-- Every even neighbour's site lies within the slack margin of the odd role's image. Selections at
  radius `Rlong` read eligibility within `r + 16` of the sites in the `Rlong`-ball around a neighbour's
  site, so the odd role's scope `r + slack` covers them (05:309–312, 861–887). -/
  slack_nbr : ∀ (y : OddRole5 n), ∀ a ∈ evenNbrs y,
    hammingDist (X.siteOf a) (X.St.oneHot (X.St.stateOf y.1)) + ht.hp.Rlong + 16 ≤ slack
  elig_local : ∀ H s j, FinProb.DependsOn (fun ω : X.CΩ ht => elig H ω s j)
    (Finset.univ.filter fun l : ht.hp.Loc => hammingDist l.1 s ≤ ht.hp.r + 16)
  valid_local : ∀ H y, FinProb.DependsOn (fun ω => valid H ω y) (X.scopeBall (h := ht) y.1 (ht.hp.r + slack))
  success_valid : ∀ H ω, success H ω → ∀ y, valid H ω y
  success_legal : ∀ H ω, success H ω → ht.hp.Legal (pos ω) (elig H ω) (X.sites ht)
  success_select : ∀ H ω, success H ω → ∀ v, (X.selLong (elig H) ω v).isSome
  valid_select : ∀ H ω y, valid H ω y → ∀ a ∈ evenNbrs y, (X.selLong (elig H) ω a).isSome
  /-- The fixed base lies in raw support. Key and array replacements keep this base; they do not
  retest global history success (05:888–894). -/
  valid_base_support : ∀ H ω y, valid H ω y → X.baseLaw.w H.1 ≠ 0
  /-- Step 1 is retained on the fixed base, including its prior cap (05:209–217).
  Later replacements alter only keys and arrays, not this certificate (05:888–894). -/
  valid_step1 : ∀ H ω y, valid H ω y → X.Step1Pass H.1
  /-- True raw block support at the observed arrays, excluding zero-normalizer fallbacks. This
  is the local support test of 05:876–879; it is recomputed at hypothetical values. -/
  valid_block_support : ∀ H ω y, valid H ω y →
    ∀ c ∈ (X.actualRecord (elig H) H ω y).2.1, ∀ i,
      X.blockWeight H c.2 c.2.2.1 (arraysOf ω c i) ≠ 0
  /-- The realized target path is supported by the full posterior, so every true prefix used
  by the high law has a positive continuation (05:483–486,601–605). -/
  valid_path_support : ∀ H ω y, valid H ω y →
    0 < X.step3PostOn H (X.actualRecord (elig H) H ω y) (arraysOf ω) none
      (H.2 (X.g.roleKey (X.p.J n) y.1))
  /-- Local prospective-position count gate, at every neighbouring query and every level
  (05:869–873). It does not require eligibility sizes on a larger domain. -/
  valid_counts : ∀ H ω y, valid H ω y → ∀ a ∈ evenNbrs y, ∀ j : Fin (ht.hp.H + 1),
    ((Finset.univ.filter fun u : CubeVertex ht.hp.d =>
      pos ω (u, j) = true ∧ hammingDist u (X.siteOf a) ≤ ht.hp.r).card : ℝ) ≤ 2 * ht.hp.lam
  valid_T : ∀ H ω y, valid H ω y →
    ((evenNbrs y).image fun a => X.selLong (elig H) ω a).card ≤ X.p.T n
  valid_hits : ∀ H ω y, valid H ω y → ∀ a ∈ evenNbrs y, ∀ l k,
    X.selLong (elig H) ω a = some l → X.g.optionalKey (X.p.J n) a.1 = some (.inl k) →
      X.p.usedBlocks n ≤ (X.hitSet (arraysOf ω) (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k)).card
  valid_heavy : ∀ H ω y, valid H ω y → ∀ a ∈ evenNbrs y, ∀ c,
    X.evenRefOf (elig H) H ω a = some c →
      (X.heavyCount H ω a c : ℝ) ≤ X.p.nu0 * (X.refLen (X.g.evenType (X.p.J n) a.1) c.2 : ℝ)
  valid_gate : ∀ H ω y, valid H ω y →
    X.candGateOn H (X.actualRecord (elig H) H ω y) (arraysOf ω) (H.2 (X.g.roleKey (X.p.J n) y.1))
  valid_step3 : ∀ H ω y, valid H ω y → ¬ X.step3FailOn H (X.actualRecord (elig H) H ω y) (arraysOf ω)

/-- The displayed star tests, with one common definition for both height truncations
(05:869–894). Step 1 belongs to the fixed base; all other tests use the replaced keys and arrays. -/
def LocalValidAt (ht : X.HeightChoice5) (elig : X.KeyHist → X.CΩ ht → ht.hp.EligMap)
    (H : X.KeyHist) (ω : X.CΩ ht) (R : ℕ) (y : OddRole5 n) : Prop :=
  let r := X.actualRecordAt (elig H) H ω R y
  X.baseLaw.w H.1 ≠ 0 ∧ X.Step1Pass H.1 ∧
  (∀ a ∈ evenNbrs y, (X.selAt (elig H) ω R a).isSome) ∧
  (∀ a ∈ evenNbrs y, ∀ j : Fin (ht.hp.H + 1),
    ((Finset.univ.filter fun u : CubeVertex ht.hp.d =>
      pos ω (u, j) = true ∧ hammingDist u (X.siteOf a) ≤ ht.hp.r).card : ℝ) ≤ 2 * ht.hp.lam) ∧
  ((evenNbrs y).image fun a => X.selAt (elig H) ω R a).card ≤ X.p.T n ∧
  (∀ a ∈ evenNbrs y, ∀ l k, X.selAt (elig H) ω R a = some l →
    X.g.optionalKey (X.p.J n) a.1 = some (.inl k) →
    X.p.usedBlocks n ≤ (X.hitSet (arraysOf ω) (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k)).card) ∧
  (∀ a ∈ evenNbrs y, ∀ l, X.selAt (elig H) ω R a = some l →
    let c := (l, X.refSubset H ω a l)
    (X.heavyCount H ω a c : ℝ) ≤ X.p.nu0 * (X.refLen (X.g.evenType (X.p.J n) a.1) c.2 : ℝ)) ∧
  (∀ c ∈ r.2.1, ∀ i, X.blockWeight H c.2 c.2.2.1 (arraysOf ω c i) ≠ 0) ∧
  0 < X.step3PostOn H r (arraysOf ω) none (H.2 (X.g.roleKey (X.p.J n) y.1)) ∧
  X.candGateOn H r (arraysOf ω) (H.2 (X.g.roleKey (X.p.J n) y.1)) ∧
  ¬ X.step3FailOn H r (arraysOf ω)

/-- Raw mass of a valid short presentation with its recorded observations. Unrecorded arrays
are integrated under their laws at the candidate history (05:905–933,978–985). -/
def shortPresentationMass (L : X.CentreLayer5) (H : X.KeyHist) (y : OddRole5 n)
    (r : X.RecordOn L.ht.hp.Loc) (a : X.ArraysOn L.ht.hp.Loc) : ℝ :=
  (X.centreLaw L.ht H).pr fun ω =>
    X.LocalValidAt L.ht L.elig H ω (L.ht.hp.Rshort (X.p.m n)) y ∧
    X.actualRecordAt (L.elig H) H ω (L.ht.hp.Rshort (X.p.m n)) y = r ∧
    ∀ c ∈ r.2.1, arraysOf ω c = a c

/-- Certificates for the paper's low-row layer. The short presentation is local in low keys,
and size failure is negligible at good histories; neither follows from center locality alone.
`Ckey` is chosen before the parameter request and dimension threshold (05:978–1001). -/
structure LowLayer5 (L : X.CentreLayer5) (Ckey : ℕ) (cL cH : ℝ) : Prop where
  /-- Validity is exactly the displayed star tests, also used by the short calculation (05:869–887). -/
  valid_eq : ∀ H ω y, L.valid H ω y ↔ X.LocalValidAt L.ht L.elig H ω L.ht.hp.Rlong y
  /-- Equality of these finite presentation masses retains locality after integrating every
  unconsulted array. It includes eligibility, validity and lookup inputs at hypothetical keys. -/
  presentation_local : ∀ b hi y r a, FinProb.DependsOn
    (fun lo => X.shortPresentationMass L (b, X.joinHidden hi lo) y r a)
    (Finset.univ.filter fun k : X.LowIdx =>
      hammingDist k.2.1 (X.g.sign y.1) ≤ Ckey * Nat.sqrt (X.p.m n))
  /-- The paper's exp(-Ω(n)) bound implies this weaker eventual bound, still sufficient
  after multiplying by the low cap exp(m^.15) (05:837–849,987–1001). -/
  size_failure : ∀ H, X.KeyGood5 H cL cH →
    (X.centreLaw L.ht H).pr (fun ω => ¬ L.ht.hp.Legal (pos ω) (L.elig H ω) (X.sites L.ht)) ≤
      Real.exp (-Real.sqrt n)

/-! ### High rows: the common law of L5.1g (05:472–605) -/

/-- The high-row model at a feasible high record: a single datum, the next-coordinate conditionals as source,
the smoothed deletion conditionals, lengths `k_c`, cap `D_H` and cost bound `a₄`. -/
def highModel {Id : Type} [DecidableEq Id] (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (hc : X.HighCapped H r a) (hpf : X.HighPriceFeasible H r a) :
    HighRowModel5 Unit {c // c ∈ X.refsOn H r a} (colLen5 (X.p.s n) r.1) N where
  raw := FinProb.dirac5 ()
  good := fun _ => True
  errorExponent := 0
  failure_bound := by simp [FinProb.pr]
  source := fun _ h => X.highSource H r a h
  deleted := fun _ c h => X.highDeleted H r a c.1 h
  length := fun c => X.refLen c.1.2.1 c.1.2.2
  capExponent := X.p.DH n
  costBound := X.p.a 4
  capped_feasible := fun _ _ => hc
  price_feasible := fun _ _ price h0 h1 => by
    obtain ⟨R, hcap, hsupp, hcost⟩ := hpf price h0 h1
    exact ⟨R, hcap, hsupp, by simpa [mul_comm] using hcost⟩

/-- A choice of common high-row law at every feasible high record, with the conclusions of L5.1g. -/
structure HighChoice5 (Id : Type) [DecidableEq Id] where
  law : ∀ (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id),
    X.HighCapped H r a → X.HighPriceFeasible H r a → FinProb (Fin (colLen5 (X.p.s n) r.1) × Fin N)
  cap : ∀ H r a hc hpf h y, (law H r a hc hpf).w (h, y) ≤
    2 * Real.exp (X.p.DH n) / ((colLen5 (X.p.s n) r.1 : ℝ) * N)
  support : ∀ H r a hc hpf h y, (law H r a hc hpf).w (h, y) ≠ 0 → (X.highSource H r a h).w y ≠ 0
  cost : ∀ H r a hc hpf, ∀ c ∈ X.refsOn H r a, ∑ h, ∑ y, (law H r a hc hpf).w (h, y) *
    highDeletionCost5 (law H r a hc hpf) (fun c' h' => X.highDeleted H r a c' h') c h y ≤
      X.p.a 4 * (X.refLen c.2.1 c.2.2 : ℝ)

/-- Outputs of an odd role: an index (`0` at low roles, `< s` at high roles) and a label. -/
abbrev OddOut := Fin (X.p.s n + 1) × Fin N

/-- The column index of an output, inside the column length of key `ℓ`. -/
def idxOf (ℓ : X.Key) (o : X.OddOut) : Option (Fin (colLen5 (X.p.s n) ℓ)) :=
  if hi : (o.1 : ℕ) < colLen5 (X.p.s n) ℓ then some ⟨o.1, hi⟩ else none

/-- The positive log deletion cost of a high output against the smoothed deletion conditional of a reference
(05:1066–1072). -/
def highCost {Id : Type} [DecidableEq Id] (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (R : X.OddOut → ℝ) (o : X.OddOut) : ℝ :=
  match X.idxOf r.1 o with
  | some h => max 0 (Real.log (R o / ((X.highDeleted H r a c h).w o.2 / (X.p.s n : ℝ))))
  | none => 0

/-- The high rows (05:592–605): on valid high roles the chosen common law at the actual record; zero otherwise.
They are probability laws on valid roles, capped by `2e^{D_H}/(sN)`, supported on labels hitting every needed
tuple, with deletion costs at most `a₄ k_c`, and read only the center data within radius `r + slack`. -/
structure HighRows5 (L : X.CentreLayer5) where
  row : X.KeyHist → X.CΩ L.ht → OddRole5 n → X.OddOut → ℝ
  row_nonneg : ∀ H ω y o, 0 ≤ row H ω y o
  row_low : ∀ H ω y o, X.g.low (X.p.J n) y.1 → row H ω y o = 0
  row_index : ∀ H ω y o, X.p.s n ≤ (o.1 : ℕ) → row H ω y o = 0
  row_invalid : ∀ H ω y o, ¬ L.valid H ω y → row H ω y o = 0
  row_sum : ∀ H ω y, L.valid H ω y → ¬ X.g.low (X.p.J n) y.1 → ∑ o, row H ω y o = 1
  row_cap : ∀ H ω y o, row H ω y o ≤ 2 * Real.exp (X.p.DH n) / ((X.p.s n : ℝ) * N)
  row_support : ∀ H ω y o, row H ω y o ≠ 0 → ∀ a ∈ evenNbrs y, ∀ c,
    X.evenRefOf (L.elig H) H ω a = some c → ∀ z ∈ X.refBlocks ω a c, X.BlockHits _ z o.2
  row_cost : ∀ H ω y, L.valid H ω y → ¬ X.g.low (X.p.J n) y.1 →
    ∀ c ∈ X.refsOn H (X.actualRecord (L.elig H) H ω y) (arraysOf ω),
      ∑ o, row H ω y o * X.highCost H (X.actualRecord (L.elig H) H ω y) (arraysOf ω) c (row H ω y) o ≤
        X.p.a 4 * (X.refLen c.2.1 c.2.2 : ℝ)
  row_local : ∀ H y, FinProb.DependsOn (fun ω => row H ω y) (X.scopeBall (h := L.ht) y.1 (L.ht.hp.r + L.slack))

namespace Lane_opus_s05

/-! ### L5.1g rows: the remaining locality (lane opus-s05) -/

/-- SUB-LEMMA G1 (05:592–605,861–887): at a valid high role, the actual long record and its
observed arrays are determined by the center data in the role's scope. Each neighbour's selection
at radius `Rlong` reads presence, activations and ties within `Rlong + r + 8`, and eligibility
within `Rlong + r + 16`, of its site (`elig_local`); the observed arrays sit within `r` of it
(`elig_shape`). `slack_nbr` puts all of these inside `scopeBall y (r + slack)`. -/
theorem highRecord_local (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (H : X.KeyHist)
    (y : OddRole5 n) (ω ω' : X.CΩ L.ht)
    (hω : ∀ l ∈ X.scopeBall (h := L.ht) y.1 (L.ht.hp.r + L.slack), ω l = ω' l)
    (hv : L.valid H ω y) (hv' : L.valid H ω' y) (hy : ¬ X.g.low (X.p.J n) y.1) :
    X.actualRecord (L.elig H) H ω y = X.actualRecord (L.elig H) H ω' y ∧
      ∀ c ∈ (X.actualRecord (L.elig H) H ω y).2.1, arraysOf ω c = arraysOf ω' c := by
  classical
  have hloc (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (l : L.ht.hp.Loc)
      (hl : _root_.hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.Rlong + L.ht.hp.r + 16) :
      ω l = ω' l := by
    apply hω l
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change _root_.hammingDist l.1 (X.St.oneHot (X.St.stateOf y.1)) ≤ L.ht.hp.r + L.slack
    have hsl : _root_.hammingDist (X.siteOf a) (X.St.oneHot (X.St.stateOf y.1)) +
        L.ht.hp.Rlong + 16 ≤ L.slack := L.slack_nbr y a ha
    have ht : _root_.hammingDist l.1 (X.St.oneHot (X.St.stateOf y.1)) ≤
        _root_.hammingDist l.1 (X.siteOf a) +
          _root_.hammingDist (X.siteOf a) (X.St.oneHot (X.St.stateOf y.1)) :=
      _root_.hammingDist_triangle l.1 (X.siteOf a) (X.St.oneHot (X.St.stateOf y.1))
    omega
  have hsel (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
      X.selAt (L.elig H) ω L.ht.hp.Rlong a = X.selAt (L.elig H) ω' L.ht.hp.Rlong a := by
    apply Lane_sol_s05_g1.selectionAt_congr_local
    · intro s hs j
      apply L.elig_local H s j ω ω'
      intro l hl
      have hd : _root_.hammingDist l.1 s ≤ L.ht.hp.r + 16 := (Finset.mem_filter.mp hl).2
      apply hloc a ha l
      have ht := _root_.hammingDist_triangle l.1 s (X.siteOf a)
      omega
    · intro s hs j l hl
      exact (L.elig_shape H ω s j l hl).2.2
    · intro l hl
      change _root_.hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.Rlong + L.ht.hp.r + 8 at hl
      exact congrArg (fun z : X.CVal L.ht => z.1) (hloc a ha l (by omega))
    · intro l hl
      change _root_.hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.Rlong + L.ht.hp.r + 8 at hl
      exact congrArg (fun z : X.CVal L.ht => z.2.1) (hloc a ha l (by omega))
    · intro j
      exact congrArg (fun z : X.CVal L.ht => z.2.2.1)
        (hloc a ha (X.siteOf a, j) (by rw [_root_.hammingDist_self]; omega))
  constructor
  · dsimp only [actualRecord, actualRecordAt]
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
    · apply Finset.biUnion_congr rfl
      intro a ha
      rw [hsel a ha]
    · apply Finset.biUnion_congr rfl
      intro a ha
      rw [hsel a ha]
    · change ¬ X.g.severity y.1 ≤ X.p.J n at hy
      simp only [ChunkGeometry5.roleKey, dif_neg hy]
  · intro c hc
    change c ∈ (evenNbrs y).biUnion _ at hc
    obtain ⟨a, ha, hc⟩ := Finset.mem_biUnion.mp hc
    cases hs : X.selAt (L.elig H) ω L.ht.hp.Rlong a with
    | none => simp only [hs, Finset.notMem_empty] at hc
    | some l =>
      have he : c = (l, X.g.evenType (X.p.J n) a.1) := by
        simpa only [hs, Finset.mem_singleton] using hc
      subst c
      obtain ⟨j, hj⟩ := Lane_sol_s05_g1.selectionAt_mem L.ht.hp (X.sites L.ht)
        (pos ω) (act ω) (L.elig H ω) (tie ω) L.ht.hp.Rlong (X.siteOf a) l hs
      have hd : _root_.hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.r :=
        (L.elig_shape H ω (X.siteOf a) j l hj).2.2
      exact congrArg (fun z : X.CVal L.ht => z.2.2.2 (X.g.evenType (X.p.J n) a.1))
        (hloc a ha l (by omega))

end Lane_opus_s05

/-- L5.1g, row construction (05:592–605): given a choice of common laws with the conclusions of L5.1g, the high
rows are that law at the actual record of each valid high role — feasible there by the high Step 3 test in local
validity, with supported raw blocks and a supported true posterior path. -/
theorem L5_1g_rows : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G)
    (L : X.CentreLayer5), (∀ x : CubeVertex n, ∀ ℓ ∈ X.g.typeKeys (X.p.J n) x, (X.g.key x).1 ∈ binList5 ℓ.coarse) →
    X.HighChoice5 L.ht.hp.Loc → Nonempty (X.HighRows5 L) := by
  classical
  intro n N E G X L hcover Ch
  let rActual := fun H ω y => X.actualRecord (L.elig H) H ω y
  have hkey (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n) :
      (rActual H ω y).1 = X.g.roleKey (X.p.J n) y.1 := rfl
  have hlen (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n)
      (hy : ¬ X.g.low (X.p.J n) y.1) : colLen5 (X.p.s n) (rActual H ω y).1 = X.p.s n := by
    rw [hkey]
    change ¬ X.g.severity y.1 ≤ X.p.J n at hy
    simp only [ChunkGeometry5.roleKey, dif_neg hy, colLen5]
  have hmask (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n)
      (hy : ¬ X.g.low (X.p.J n) y.1) : (rActual H ω y).2.2.2 = none := by
    change ¬ X.g.severity y.1 ≤ X.p.J n at hy
    simp only [rActual, actualRecord, actualRecordAt, ChunkGeometry5.roleKey, dif_neg hy]
  have href (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n) :
      ∀ c ∈ (rActual H ω y).2.2.1, (c.1, c.2.1) ∈ (rActual H ω y).2.1 := by
    intro c hc
    change c ∈ (evenNbrs y).biUnion _ at hc
    obtain ⟨a, ha, hc⟩ := Finset.mem_biUnion.mp hc
    cases hs : X.selAt (L.elig H) ω L.ht.hp.Rlong a with
    | none => simp [hs] at hc
    | some l =>
      by_cases ht : X.g.roleKey (X.p.J n) y.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          (X.g.roleKey (X.p.J n) y.1).isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome
      · have he : c = (l, X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1) := by
          simpa only [hs, if_pos ht, Finset.mem_singleton] using hc
        subst c
        apply Finset.mem_biUnion.mpr
        exact ⟨a, ha, by simp [hs]⟩
      · simp only [hs, if_neg ht, Finset.notMem_empty] at hc
  have hfeasible (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n)
      (hv : L.valid H ω y) (hy : ¬ X.g.low (X.p.J n) y.1) :
      X.HighCapped H (rActual H ω y) (arraysOf ω) ∧ X.HighPriceFeasible H (rActual H ω y) (arraysOf ω) := by
    have hr : (rActual H ω y).1.isRight := by
      rw [hkey]
      change ¬ X.g.severity y.1 ≤ X.p.J n at hy
      simp [ChunkGeometry5.roleKey, hy]
    by_contra hf
    apply L.valid_step3 H ω y hv
    exact ⟨L.valid_gate H ω y hv, Or.inr (Or.inr ⟨hr, hf⟩)⟩
  let obs := fun H ω y => Lane_sol_s05_centres.observedArrays X (rActual H ω y) (arraysOf ω)
  have hobs (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n) :
      ∀ c ∈ (rActual H ω y).2.1, arraysOf ω c = obs H ω y c := by
    intro c hc
    exact (Lane_sol_s05_centres.observedArrays_eq X _ _ c hc).symm
  have hcanon (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n)
      (hv : L.valid H ω y) (hy : ¬ X.g.low (X.p.J n) y.1) :
      X.HighCapped H (rActual H ω y) (obs H ω y) ∧ X.HighPriceFeasible H (rActual H ω y) (obs H ω y) := by
    have hm : ∀ c M, (rActual H ω y).2.2.2 = some (c.1, c.2, M) → c ∈ (rActual H ω y).2.1 := by
      intro c M hc
      rw [hmask H ω y hy] at hc
      cases hc
    exact ⟨(Lane_sol_s05_centres.highCapped_arrays_congr X H _ _ _ hm (hobs H ω y)).mp
        (hfeasible H ω y hv hy).1,
      (Lane_sol_s05_centres.highPrice_arrays_congr X H _ _ _ hm (href H ω y) (hobs H ω y)).mp
        (hfeasible H ω y hv hy).2⟩
  let law := fun H ω y hv hy => Ch.law H (rActual H ω y) (obs H ω y)
    (hcanon H ω y hv hy).1 (hcanon H ω y hv hy).2
  let row : X.KeyHist → X.CΩ L.ht → OddRole5 n → X.OddOut → ℝ := fun H ω y o =>
    if hv : L.valid H ω y then
      if hy : ¬ X.g.low (X.p.J n) y.1 then Lane_sol_s05_centres.indexRow (law H ω y hv hy) (X.p.s n) o
      else 0
    else 0
  have hrow (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n)
      (hv : L.valid H ω y) (hy : ¬ X.g.low (X.p.J n) y.1) (o : X.OddOut) :
      row H ω y o = Lane_sol_s05_centres.indexRow (law H ω y hv hy) (X.p.s n) o := by
    simp [row, hv, hy]
  refine ⟨
    { row := row
      row_nonneg := ?_
      row_low := ?_
      row_index := ?_
      row_invalid := ?_
      row_sum := ?_
      row_cap := ?_
      row_support := ?_
      row_cost := ?_
      row_local := ?_ }⟩
  · intro H ω y o
    by_cases hv : L.valid H ω y
    · by_cases hy : ¬ X.g.low (X.p.J n) y.1
      · rw [hrow H ω y hv hy]
        exact Lane_sol_s05_centres.indexRow_nonneg _ _ _
      · have hl : X.g.low (X.p.J n) y.1 := Classical.not_not.mp hy
        simp [row, hv, hl]
    · simp [row, hv]
  · intro H ω y o hy
    simp [row, hy]
  · intro H ω y o hi
    by_cases hv : L.valid H ω y
    · by_cases hy : ¬ X.g.low (X.p.J n) y.1
      · rw [hrow H ω y hv hy]
        exact Lane_sol_s05_centres.indexRow_index _ (hlen H ω y hy) o hi
      · simp [row, hv, hy]
    · simp [row, hv]
  · intro H ω y o hv
    simp [row, hv]
  · intro H ω y hv hy
    simp only [hrow H ω y hv hy]
    exact Lane_sol_s05_centres.indexRow_sum _ (hlen H ω y hy)
  · intro H ω y o
    have hC : 0 ≤ 2 * Real.exp (X.p.DH n) / ((X.p.s n : ℝ) * N) := by positivity
    by_cases hv : L.valid H ω y
    · by_cases hy : ¬ X.g.low (X.p.J n) y.1
      · rw [hrow H ω y hv hy]
        apply Lane_sol_s05_centres.indexRow_cap _ _ hC
        intro h x
        simpa only [hlen H ω y hy] using Ch.cap H (rActual H ω y) (obs H ω y)
          (hcanon H ω y hv hy).1 (hcanon H ω y hv hy).2 h x
      · have hl : X.g.low (X.p.J n) y.1 := Classical.not_not.mp hy
        simpa [row, hv, hl] using hC
    · simpa [row, hv] using hC
  · intro H ω y o ho a ha c hsel z hz
    have hv : L.valid H ω y := by
      by_contra hv
      exact ho (by simp [row, hv])
    have hy : ¬ X.g.low (X.p.J n) y.1 := by
      by_contra hy
      exact ho (by simp [row, hy])
    rw [hrow H ω y hv hy] at ho
    obtain ⟨h, _, hpos⟩ := Lane_sol_s05_centres.indexRow_support _ o ho
    have hsource : (X.highSource H (rActual H ω y) (arraysOf ω) h).w o.2 ≠ 0 := by
      have hp := Ch.support H (rActual H ω y) (obs H ω y) (hcanon H ω y hv hy).1
        (hcanon H ω y hv hy).2 h o.2 hpos
      have hm : ∀ c M, (rActual H ω y).2.2.2 = some (c.1, c.2, M) → c ∈ (rActual H ω y).2.1 := by
        intro c M hc
        rw [hmask H ω y hy] at hc
        cases hc
      rw [Lane_sol_s05_centres.highSource_arrays_congr X H _ _ _ hm (hobs H ω y)]
      exact hp
    cases hs : X.selLong (L.elig H) ω a with
    | none => simp [evenRefOf, hs] at hsel
    | some l =>
      have hc : c = (l, X.refSubset H ω a l) := by simpa [evenRefOf, hs] using hsel.symm
      subst c
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hobsMem : (l, X.g.evenType (X.p.J n) a.1) ∈ (rActual H ω y).2.1 := by
        apply Finset.mem_biUnion.mpr
        refine ⟨a, ha, ?_⟩
        have hsa : X.selAt (L.elig H) ω L.ht.hp.Rlong a = some l := hs
        simp [hsa]
      have hkeyMem : (rActual H ω y).1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 := by
        have hadj : (cube n).Adj a.1 y.1 := by
          have hh := (Finset.mem_filter.mp ha).2
          exact hh
        rcases (L5_1e_cover X.g (X.p.J n)).1 a.1 y.1 hadj with hkey' | hopt
        · simpa [hkey, ChunkGeometry5.evenType] using hkey'
        · have hh : ¬ X.g.severity y.1 ≤ X.p.J n := hy
          simp [ChunkGeometry5.optionalKey, ChunkGeometry5.roleKey, hh] at hopt
      exact Lane_sol_s05_centres.high_source_block_hits X H (rActual H ω y) (arraysOf ω)
        (L.valid_base_support H ω y hv) (L.valid_path_support H ω y hv)
        (l, X.g.evenType (X.p.J n) a.1) hobsMem hkeyMem
        (hcover a.1 _ (by simpa [hkey, ChunkGeometry5.evenType] using hkeyMem))
        (Lane_q_s05_hist1b.typeSegs_le_keyPrefix5 X _ ⟨a.1, a.2, rfl⟩ _ hkeyMem) i
        (L.valid_block_support H ω y hv _ hobsMem i) h o.2 hsource
  · intro H ω y hv hy c hc
    let R := law H ω y hv hy
    have hm : ∀ c M, (rActual H ω y).2.2.2 = some (c.1, c.2, M) → c ∈ (rActual H ω y).2.1 := by
      intro c M hc
      rw [hmask H ω y hy] at hc
      cases hc
    have hrefs := Lane_sol_s05_centres.refsOn_arrays_congr X H (rActual H ω y)
      (arraysOf ω) (obs H ω y) (href H ω y) (hobs H ω y)
    have hc' : c ∈ X.refsOn H (rActual H ω y) (obs H ω y) := by rw [← hrefs]; exact hc
    have hd : ∀ c h, X.highDeleted H (rActual H ω y) (arraysOf ω) c h =
        X.highDeleted H (rActual H ω y) (obs H ω y) c h :=
      Lane_sol_s05_centres.highDeleted_arrays_congr X H _ _ _ hm (hobs H ω y)
    have he (o : X.OddOut) : X.highCost H (rActual H ω y) (arraysOf ω) c (row H ω y) o =
        Lane_sol_s05_centres.indexCost R
          (fun c' h' => X.highDeleted H (rActual H ω y) (arraysOf ω) c' h') c (X.p.s n) o := by
      dsimp [highCost, idxOf, Lane_sol_s05_centres.indexCost]
      split_ifs
      · simp only [hrow H ω y hv hy, hlen H ω y hy, R]
      · rfl
    change (∑ o, row H ω y o * X.highCost H (rActual H ω y) (arraysOf ω) c (row H ω y) o) ≤ _
    simp only [he, hrow H ω y hv hy]
    change (∑ o, Lane_sol_s05_centres.indexRow R (X.p.s n) o *
      Lane_sol_s05_centres.indexCost R
        (fun c' h' => X.highDeleted H (rActual H ω y) (arraysOf ω) c' h') c (X.p.s n) o) ≤ _
    rw [Lane_sol_s05_centres.indexCost_sum R
      (fun c' h' => X.highDeleted H (rActual H ω y) (arraysOf ω) c' h') c (hlen H ω y hy)]
    have hcost := Ch.cost H (rActual H ω y) (obs H ω y) (hcanon H ω y hv hy).1
      (hcanon H ω y hv hy).2 c hc'
    simpa only [R, law, hd] using hcost
  · intro H y
    intro ω ω' hω
    have hvEq := L.valid_local H y ω ω' hω
    dsimp only at hvEq
    by_cases hv : L.valid H ω y
    · have hv' : L.valid H ω' y := hvEq ▸ hv
      by_cases hy : ¬ X.g.low (X.p.J n) y.1
      · funext o
        dsimp only
        rw [hrow H ω y hv hy, hrow H ω' y hv' hy]
        obtain ⟨hr, ha⟩ := Lane_opus_s05.highRecord_local X L H y ω ω' hω hv hv' hy
        have hobsEq : obs H ω y = obs H ω' y := by
          show Lane_sol_s05_centres.observedArrays X (rActual H ω y) (arraysOf ω) =
            Lane_sol_s05_centres.observedArrays X (rActual H ω' y) (arraysOf ω')
          rw [← show rActual H ω y = rActual H ω' y from hr]
          funext c
          simp only [Lane_sol_s05_centres.observedArrays]
          split_ifs with hc
          · exact ha c hc
          · rfl
        have key : ∀ (r r' : X.RecordOn L.ht.hp.Loc) (a a' : X.ArraysOn L.ht.hp.Loc)
            (hc : X.HighCapped H r a) (hp : X.HighPriceFeasible H r a)
            (hc' : X.HighCapped H r' a') (hp' : X.HighPriceFeasible H r' a'), r = r' → a = a' →
            Lane_sol_s05_centres.indexRow (Ch.law H r a hc hp) (X.p.s n) o =
              Lane_sol_s05_centres.indexRow (Ch.law H r' a' hc' hp') (X.p.s n) o := by
          intro r r' a a' hc hp hc' hp' h1 h2
          subst h1
          subst h2
          rfl
        exact key _ _ _ _ _ _ _ _ hr hobsEq
      · have hl : X.g.low (X.p.J n) y.1 := Classical.not_not.mp hy
        simp [row, hv, hv', hl]
    · have hv' : ¬ L.valid H ω' y := by simpa only [← hvEq] using hv
      simp [row, hv, hv']

/-! ### Low rows: the selection adjustment of L5.1k (05:896–1001) -/

/-- The low rows (05:896–1001).  `row` is the long-rule row, `proxy` its short-rule proxy mean
`p̄^{pr}_b(y;H)`.  For every fixed base, high history, low role and other low columns, `selExp` is the
finite target/presentation experiment of the selection table, with prior `π_ℓ`, whose mean identity integrates the target prior and the
raw centers. The row constructor bounds `proxyRadius` by a constant chosen before the dimension threshold. -/
structure LowRows5 (L : X.CentreLayer5) (cL cH : ℝ) where
  row : X.KeyHist → X.CΩ L.ht → OddRole5 n → X.OddOut → ℝ
  proxy : X.KeyHist → OddRole5 n → Fin N → ℝ
  row_nonneg : ∀ H ω y o, 0 ≤ row H ω y o
  row_high : ∀ H ω y o, ¬ X.g.low (X.p.J n) y.1 → row H ω y o = 0
  row_index : ∀ H ω y o, (o.1 : ℕ) ≠ 0 → row H ω y o = 0
  row_invalid : ∀ H ω y o, ¬ L.valid H ω y → row H ω y o = 0
  row_sum : ∀ H ω y, L.valid H ω y → X.g.low (X.p.J n) y.1 → ∑ o, row H ω y o = 1
  row_cap : ∀ H ω y o, (N : ℝ) * row H ω y o ≤ Real.exp (X.p.DL n)
  row_support : ∀ H ω y o, row H ω y o ≠ 0 → ∀ a ∈ evenNbrs y, ∀ c,
    X.evenRefOf (L.elig H) H ω a = some c → ∀ z ∈ X.refBlocks ω a c, X.BlockHits _ z o.2
  row_deletion : ∀ H ω y, L.valid H ω y → X.g.low (X.p.J n) y.1 →
    ∀ c ∈ X.refsOn H (X.actualRecord (L.elig H) H ω y) (arraysOf ω), ∀ o,
      row H ω y o ≤ Real.exp (X.p.a 4 * X.refLen c.2.1 c.2.2) *
        X.step3PostOn H (X.actualRecord (L.elig H) H ω y) (arraysOf ω) (some c) (fun _ => o.2)
  row_local : ∀ H y, FinProb.DependsOn (fun ω => row H ω y) (X.scopeBall (h := L.ht) y.1 (L.ht.hp.r + L.slack))
  long_vs_proxy : ∀ H, X.KeyGood5 H cL cH → ∀ y x, X.g.low (X.p.J n) y.1 →
    (X.centreLaw L.ht H).expect (fun ω => (N : ℝ) * row H ω y (0, x)) ≤ proxy H y x + 1
  proxy_nonneg : ∀ H y x, 0 ≤ proxy H y x
  proxy_high : ∀ H y x, ¬ X.g.low (X.p.J n) y.1 → proxy H y x = 0
  proxy_cap : ∀ H y x, proxy H y x ≤ Real.exp (X.p.DL n)
  proxyRadius : ℕ
  proxy_local : ∀ b hi y, FinProb.DependsOn (fun lo => proxy (b, X.joinHidden hi lo) y)
    (Finset.univ.filter fun k : X.LowIdx =>
      hammingDist k.2.1 (X.g.sign y.1) ≤ proxyRadius * Nat.sqrt (X.p.m n))
  Data : X.Base → X.HighHid → OddRole5 n → Type
  dataFintype : ∀ b hi y, Fintype (Data b hi y)
  /-- The experiment fixes the key history except the target, so it also reads the other low
  columns `lo` (05:898–903); the target column of `lo` is overwritten in `selExp_mean`. -/
  selExp : ∀ b hi y (lo : X.LowHid), @SelectionExperiment5 (Fin N) (Data b hi y) _ (dataFintype b hi y)
  selExp_prior : ∀ b hi y lo, X.g.low (X.p.J n) y.1 →
    (selExp b hi y lo).prior = X.prior b (X.g.roleKey (X.p.J n) y.1)
  selExp_records : ∀ b hi y lo, Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1))) *
    (selExp b hi y lo).recordBound ≤ 1
  selExp_mean : ∀ b hi y lo x, X.g.low (X.p.J n) y.1 →
    ∑ y', (X.prior b (X.g.roleKey (X.p.J n) y.1)).w y' *
        proxy (b, X.joinHidden hi (Function.update lo (X.lowIdxOf (X.g.roleKey (X.p.J n) y.1))
          (fun _ => y'))) y x =
      (N : ℝ) * @Finset.sum (Data b hi y) ℝ _ (@Finset.univ _ (dataFintype b hi y)) (fun d =>
        (selExp b hi y lo).selectedMass d *
          (selExp b hi y lo).proxyRow (Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1)))) d x)

attribute [instance] LowRows5.dataFintype

/-! ### Lane opus-s05: sub-lemmas of L5.1j and L5.1k (rows)

`L5_1j` is assembled from the marking eligibility `markElig` (05:818–833), its locality, maximality
and probability estimates; `L5_1k_rows` from a selection table `LowTable5` (05:896–985) and the
long/short comparison (05:987–1001). Each `sorry` below is one open sub-lemma. -/

namespace Lane_opus_s05

open scoped BigOperators

set_option maxHeartbeats 400000

/-! ## L5.1j -/

section J

/-- The height device fixed from `α` (05:315–329). -/
def canonHt : X.HeightChoice5 where
  b₀ := X.p.alpha / 10000
  b := X.p.alpha / 2000
  σ := X.p.alpha / 1000000
  ζ := X.p.alpha / 100000
  θ := 1 - X.p.alpha / 100000
  a := X.p.alpha / 20000
  adm := Lane_sol_s05_centres.height_admissible X.p
  regime := Lane_sol_s05_centres.heightRegime X.p
  hθ := by have := X.p.halpha.2; linarith
  hbT := by have := X.p.halpha.1; linarith
  fixed := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The long radius fits the canonical slack. -/
theorem canonHt_slack_large : (canonHt X).hp.Rlong + 32 ≤ Lane_sol_s05_centres.centreSlack X.p n := by
  simp only [HDParams.Rlong, HeightChoice5.hp, canonHt, Lane_sol_s05_centres.centreSlack]
  omega

variable (ht : X.HeightChoice5)

/-- Prospective IDs at a site and level (05:820–824). -/
def prosp (P : ht.hp.Loc → Bool) (s : CubeVertex ht.hp.d) (j : ℕ) : Finset ht.hp.Loc :=
  Finset.univ.filter fun l => P l = true ∧ (l.2 : ℕ) = j ∧ hammingDist l.1 s ≤ ht.hp.r

/-- The record of an odd role for given choices at its even neighbours: the body of
`actualRecordAt` with the selections replaced by `σ` (05:331–343). -/
def recordOf (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc) (σ : EvenRole5 n → Option ht.hp.Loc)
    (y : OddRole5 n) : X.RecordOn ht.hp.Loc :=
  let ℓ := X.g.roleKey (X.p.J n) y.1
  let obs : Finset (ht.hp.Loc × X.Ty) := (evenNbrs y).biUnion fun a =>
    match σ a with
    | some l => {(l, X.g.evenType (X.p.J n) a.1)}
    | none => ∅
  let refs : Finset (ht.hp.Loc × X.Ty × Option X.Key) := (evenNbrs y).biUnion fun a =>
    match σ a with
    | some l =>
      if ℓ ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          ℓ.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome then
        {(l, X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)} else ∅
    | none => ∅
  let mask : Option (ht.hp.Loc × X.Ty × Finset (Fin X.blockBound)) :=
    match ℓ with
    | .inl k =>
      if hex : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ a).isSome then
        let a := Classical.choose hex
        match σ a with
        | some l =>
          some (l, X.g.evenType (X.p.J n) a.1,
            X.firstK (X.hitSet A (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k))
              (X.p.usedBlocks n))
        | none => none
      else none
    | .inr _ => none
  (ℓ, obs, refs, mask)

theorem actualRecordAt_eq (elig : X.CΩ ht → ht.hp.EligMap) (H : X.KeyHist) (ω : X.CΩ ht) (R : ℕ)
    (y : OddRole5 n) :
    X.actualRecordAt elig H ω R y = recordOf X ht H (arraysOf ω) (fun a => X.selAt elig ω R a) y := rfl

/-- `heavyCount` on a given array assignment. -/
def heavyCountOn (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc) (v : EvenRole5 n) (c : X.CRef ht) : ℕ :=
  ∑ i : Fin (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1)),
    if ∃ j ∈ c.2, X.blockIdx _ j = some i then
      (Finset.univ.filter fun e : Fin (X.p.typeSegs n (X.g.evenType (X.p.J n) v.1)) × Fin X.p.q0 =>
        X.PriorHeavy H (X.g.evenType (X.p.J n) v.1)
          (A (c.1, X.g.evenType (X.p.J n) v.1) i e.1 e.2)).card
    else 0

/-- The singleton tests of an ID for an even role: prior-heavy fraction and optional hits (05:820–824). -/
def singletonOK (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc) (v : EvenRole5 n) (l : ht.hp.Loc) : Prop :=
  let c : X.CRef ht := (l, X.refSubsetOn H A (l, X.g.evenType (X.p.J n) v.1) (X.g.optionalKey (X.p.J n) v.1))
  (heavyCountOn X ht H A v c : ℝ) ≤ X.p.nu0 * (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) ∧
    ∀ k, X.g.optionalKey (X.p.J n) v.1 = some (.inl k) →
      X.p.usedBlocks n ≤ (X.hitSet A (l, X.g.evenType (X.p.J n) v.1) (X.lowCol H.2 k)).card

/-- Failed ID sets at an odd state `b` on levels `j, j+1`: mappings of all neighbouring even states
into prospective IDs with at most `T` IDs whose record fails Step 3 at some role of `b`
(05:826–833). -/
def failSets (H : X.KeyHist) (P : ht.hp.Loc → Bool) (A : X.ArraysOn ht.hp.Loc) (b : X.St.Site) (j : ℕ) :
    Finset (Finset ht.hp.Loc) :=
  ((Finset.univ : Finset (X.St.Site → ht.hp.Loc)).filter fun μ =>
      (∀ t ∈ X.St.neighbors b, μ t ∈ prosp X ht P (X.St.oneHot t) j ∪ prosp X ht P (X.St.oneHot t) (j + 1)) ∧
      ((X.St.neighbors b).image μ).card ≤ X.p.T n ∧
      ∃ y : OddRole5 n, X.St.stateOf y.1 = b ∧
        X.step3FailOn H (recordOf X ht H A (fun a => some (μ (X.St.stateOf a.1))) y) A).image
    fun μ => (X.St.neighbors b).image μ

/-- Marked IDs at a site-level: the union of the maximal disjoint failure families of the incident
stars on the two level pairs containing it (05:828–833). -/
def marks (H : X.KeyHist) (P : ht.hp.Loc → Bool) (A : X.ArraysOn ht.hp.Loc) (s : CubeVertex ht.hp.d)
    (j : ℕ) : Finset ht.hp.Loc :=
  (((Finset.univ.filter fun b : X.St.Site => ∃ t ∈ X.St.neighbors b, X.St.oneHot t = s).biUnion fun b =>
    ((Finset.range (ht.hp.H + 1)).filter fun j' => j' = j ∨ j' + 1 = j).biUnion fun j' =>
      (Lane_sol_s05_centres.markingFamily (failSets X ht H P A b j')).biUnion id)).filter
    fun l => (l.2 : ℕ) = j

/-- Pre-activation eligibility from presence and arrays. -/
def eligOf (H : X.KeyHist) (P : ht.hp.Loc → Bool) (A : X.ArraysOn ht.hp.Loc) : ht.hp.EligMap :=
  fun s j => (prosp X ht P s j).filter fun l =>
    (∀ v : EvenRole5 n, X.siteOf v = s → singletonOK X ht H A v l) ∧ l ∉ marks X ht H P A s j

/-- The marking eligibility of L5.1j. -/
def markElig (H : X.KeyHist) (ω : X.CΩ ht) : ht.hp.EligMap := eligOf X ht H (pos ω) (arraysOf ω)

theorem markElig_preActivation (H : X.KeyHist) (ω ω' : X.CΩ ht)
    (h : ∀ l, (ω l).1 = (ω' l).1 ∧ (ω l).2.2.2 = (ω' l).2.2.2) : markElig X ht H ω = markElig X ht H ω' := by
  have hp : pos ω = pos ω' := funext fun l => (h l).1
  have ha : arraysOf ω = arraysOf ω' := funext fun c => by simp only [arraysOf, arr, (h c.1).2]
  simp only [markElig, hp, ha]

theorem markElig_shape (H : X.KeyHist) (ω : X.CΩ ht) (s : CubeVertex ht.hp.d) (j : Fin (ht.hp.H + 1))
    (l : ht.hp.Loc) (hl : l ∈ markElig X ht H ω s j) :
    pos ω l = true ∧ l.2 = j ∧ hammingDist l.1 s ≤ ht.hp.r := by
  have h := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2
  exact ⟨h.1, Fin.ext h.2.1, h.2.2⟩

/-- SUB-LEMMA J1 (05:880–887): eligibility at a site-level reads center data within `r + 16`.
Prospective sets and singleton tests read the `r`-ball; incident stars have neighbouring sites
within `8` (`CubeStates5.even_distance`), so their mappings read the `(r+8)`-ball. -/
theorem markElig_local (H : X.KeyHist) (s : CubeVertex ht.hp.d) (j : Fin (ht.hp.H + 1)) :
    FinProb.DependsOn (fun ω : X.CΩ ht => markElig X ht H ω s j)
      (Finset.univ.filter fun l : ht.hp.Loc => hammingDist l.1 s ≤ ht.hp.r + 16) := by
  sorry

/-- SUB-LEMMA J2 (05:855–860, maximality): a mapping of all neighbouring even states of an odd
role into eligible IDs on two consecutive levels with at most `T` IDs, agreeing with the
selections at the role's neighbours, passes Step 3; otherwise its ID set would be a failed set
disjoint from the marked maximal family. -/
theorem markElig_sound (H : X.KeyHist) (ω : X.CΩ ht) (R : ℕ) (y : OddRole5 n)
    (μ : X.St.Site → ht.hp.Loc) (j : ℕ) (hj : j ≤ ht.hp.H)
    (helig : ∀ t ∈ X.St.neighbors (X.St.stateOf y.1), μ t ∈ markElig X ht H ω (X.St.oneHot t) (μ t).2)
    (hlev : ∀ t ∈ X.St.neighbors (X.St.stateOf y.1), ((μ t).2 : ℕ) = j ∨ ((μ t).2 : ℕ) = j + 1)
    (hT : ((X.St.neighbors (X.St.stateOf y.1)).image μ).card ≤ X.p.T n)
    (hsel : ∀ a ∈ evenNbrs y, X.selAt (markElig X ht H) ω R a = some (μ (X.St.stateOf a.1))) :
    ¬ X.step3FailOn H (X.actualRecordAt (markElig X ht H) H ω R y) (arraysOf ω) := by
  sorry

/-- Ball counts `λ/2 .. 2λ` at every site-level (05:835–838). -/
def BallsOK (ω : X.CΩ ht) : Prop :=
  ∀ s ∈ X.sites ht, ∀ j : Fin (ht.hp.H + 1),
    ht.hp.lam / 2 ≤ ((Finset.univ.filter fun u : CubeVertex ht.hp.d =>
        pos ω (u, j) = true ∧ hammingDist u s ≤ ht.hp.r).card : ℝ) ∧
      ((Finset.univ.filter fun u : CubeVertex ht.hp.d =>
        pos ω (u, j) = true ∧ hammingDist u s ≤ ht.hp.r).card : ℝ) ≤ 2 * ht.hp.lam

/-- Small singleton losses: at most `λ/12` prospective IDs fail a singleton test at each
site-level (05:835–838). -/
def SinglesOK (H : X.KeyHist) (ω : X.CΩ ht) : Prop :=
  ∀ s ∈ X.sites ht, ∀ j : ℕ, (((prosp X ht (pos ω) s j).filter fun l =>
    ¬ ∀ v : EvenRole5 n, X.siteOf v = s → singletonOK X ht H (arraysOf ω) v l).card : ℝ) ≤ ht.hp.lam / 12

/-- Every maximal disjoint failure family has fewer than `n` members (05:838–846). -/
def FamiliesOK (H : X.KeyHist) (ω : X.CΩ ht) : Prop :=
  ∀ b j, (Lane_sol_s05_centres.markingFamily (failSets X ht H (pos ω) (arraysOf ω) b j)).card < n

/-- The geometry success event: legal eligibility, a long choice at every even role and local
validity at every odd role (05:835–860). -/
def CentreSuccess (H : X.KeyHist) (ω : X.CΩ ht) : Prop :=
  ht.hp.Legal (pos ω) (markElig X ht H ω) (X.sites ht) ∧
    (∀ v, (X.selLong (markElig X ht H) ω v).isSome) ∧
      ∀ y, X.LocalValidAt ht (markElig X ht) H ω ht.hp.Rlong y

/-- Support and true-target gate at the actual long records (05:874–879). -/
def SupportOK (H : X.KeyHist) (ω : X.CΩ ht) : Prop :=
  ∀ y, (∀ a ∈ evenNbrs y, (X.selLong (markElig X ht H) ω a).isSome) →
    let r := X.actualRecordAt (markElig X ht H) H ω ht.hp.Rlong y
    (∀ c ∈ r.2.1, ∀ i, X.blockWeight H c.2 c.2.2.1 (arraysOf ω c i) ≠ 0) ∧
      0 < X.step3PostOn H r (arraysOf ω) none (H.2 (X.g.roleKey (X.p.J n) y.1)) ∧
      X.candGateOn H r (arraysOf ω) (H.2 (X.g.roleKey (X.p.J n) y.1))

end J

/-- SUB-LEMMA J3 (05:835–838): binomial tails for prospective counts. -/
theorem balls_tail : ∀ p : Params5 γ K' χ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ H : X.KeyHist, (X.centreLaw (canonHt X) H).pr (fun ω => ¬ BallsOK X (canonHt X) ω) ≤
        Real.exp (-Real.sqrt n) / 3 := by
  sorry

/-- SUB-LEMMA J4 (05:820–824,835–838): singleton losses, from independent arrays at distinct IDs
and the per-ID `o(1)` failure probability at good histories. -/
theorem singles_tail : ∀ (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
          (X.centreLaw (canonHt X) H).pr (fun ω => BallsOK X (canonHt X) ω ∧
            ¬ SinglesOK X (canonHt X) H ω) ≤ Real.exp (-Real.sqrt n) / 3 := by
  sorry

/-- SUB-LEMMA J5 (05:838–846): `n` disjoint failures at one star read disjoint independent arrays;
the history's Step 3 rates and the record counts bound them by `exp(-Ω(n k'_j))` or
`exp(-Ω(n s))`, summable over stars and level pairs. -/
theorem families_tail : ∀ (C : ℝ) (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        X.RecordCount C → ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
          (X.centreLaw (canonHt X) H).pr (fun ω => BallsOK X (canonHt X) ω ∧
            ¬ FamiliesOK X (canonHt X) H ω) ≤ Real.exp (-Real.sqrt n) / 3 := by
  classical
  intro C cL cH hc
  refine ⟨Lane_sol_s05_j5.familyRequest C cL cH, ?_⟩
  intro p hp
  have he := (Lane_sol_s05_j5.family_size_eventually p).and
    ((Lane_sol_s05_j5.family_budget_eventually p C cL cH hc hp).and
      (Lane_sol_s05_j5.family_global_tail p))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp he
  refine ⟨n₀, ?_⟩
  intro n hn N E G X hXp hcount H hgood
  obtain ⟨⟨hn2, hT, hTsmall⟩, hbudget, htail⟩ := hn₀ n hn
  let ht : X.HeightChoice5 := canonHt X
  have hT' : 0 < X.p.T n := by simpa only [hXp] using hT
  have hlam : ht.hp.lam = (n : ℝ) ^ (10 : ℕ) := by
    simp only [ht, canonHt, HeightChoice5.hp]
    simp only [Real.rpow_ofNat]
  have hTsmall' : (X.p.T n : ℝ) ≤ ht.hp.lam / 2 := by
    simpa only [hXp, hlam] using hTsmall
  have hrec : ∀ (A : X.ArraysOn ht.hp.Loc) (μ : X.St.Site → ht.hp.Loc) (y : OddRole5 n),
      recordOf X ht H A (fun a => some (μ (X.St.stateOf a.1))) y =
        Lane_sol_s05_j5.starRecord X H A μ y := by
    intro A μ y
    unfold recordOf Lane_sol_s05_j5.starRecord
    dsimp only
    simp only [Option.isSome_some, Bool.true_eq, and_true]
    apply Prod.ext
    · rfl
    apply Prod.ext
    · ext c
      simp only [Finset.mem_biUnion, Finset.mem_singleton, Finset.mem_image, eq_comm]
    apply Prod.ext
    · ext c
      simp only [Finset.mem_biUnion, Finset.mem_singleton, Finset.mem_image, Finset.mem_filter]
      aesop
    · rfl
  have hlevel : ∀ (P : ht.hp.Loc → Bool) (s : CubeVertex ht.hp.d) (j : Fin (ht.hp.H + 1)),
      (prosp X ht P s j).card =
        (Finset.univ.filter fun u : CubeVertex ht.hp.d =>
          P (u, j) = true ∧ hammingDist u s ≤ ht.hp.r).card := by
    intro P s j
    unfold prosp
    convert Lane_sol_s05_j5.level_card ht.hp.H P
      (fun u => HypercubeRamsey.hammingDist u s ≤ ht.hp.r) j using 1 <;>
      congr 1 <;> ext l <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hout : ∀ (P : ht.hp.Loc → Bool) (s : CubeVertex ht.hp.d) (k : ℕ),
      ht.hp.H < k → prosp X ht P s k = ∅ := by
    intro P s k hk
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    have hh := (Finset.mem_filter.mp hl).2.2.1
    have hi := l.2.isLt
    omega
  let Ball (P : ht.hp.Loc → Bool) : Prop :=
    ∀ s ∈ X.sites ht, ∀ j : Fin (ht.hp.H + 1),
      ht.hp.lam / 2 ≤ ((Finset.univ.filter fun u : CubeVertex ht.hp.d =>
        P (u, j) = true ∧ HypercubeRamsey.hammingDist u s ≤ ht.hp.r).card : ℝ) ∧
      ((Finset.univ.filter fun u : CubeVertex ht.hp.d =>
        P (u, j) = true ∧ HypercubeRamsey.hammingDist u s ≤ ht.hp.r).card : ℝ) ≤ 2 * ht.hp.lam
  let Fam (P : ht.hp.Loc → Bool) (A : X.ArraysOn ht.hp.Loc) : Prop :=
    ∀ b j, (Lane_sol_s05_centres.markingFamily (failSets X ht H P A b j)).card < n
  have hcond : ∀ P : ht.hp.Loc → Bool, Ball P →
      (Lane_sol_s05_j5.arrayLaw (I := ht.hp.Loc) X H).pr (fun A => ¬ Fam P A) ≤
        Real.exp (-Real.sqrt n) / 3 := by
    intro P hP
    let Q : X.St.Site → ℕ → Finset ht.hp.Loc := fun t j => prosp X ht P (X.St.oneHot t) j
    have hupper : ∀ s ∈ X.sites ht, ∀ k : ℕ, ((prosp X ht P s k).card : ℝ) ≤ 2 * ht.hp.lam := by
      intro s hs k
      by_cases hk : k ≤ ht.hp.H
      · change ((prosp X ht P s (⟨k, by omega⟩ : Fin (ht.hp.H + 1))).card : ℝ) ≤ _
        rw [hlevel]
        exact (hP s hs ⟨k, by omega⟩).2
      · rw [hout P s k (by omega)]
        simp only [Finset.card_empty, Nat.cast_zero]
        rw [hlam]
        positivity
    have hfeq : ∀ A b j, failSets X ht H P A b j = Lane_sol_s05_j5.failureSets X H Q A b j := by
      intro A b j
      unfold failSets Lane_sol_s05_j5.failureSets
      dsimp only [Q]
      congr 1
      ext μ
      simp only [Finset.mem_filter, hrec]
    have hsingle : ∀ (y : OddRole5 n) (j : Fin (ht.hp.H + 1)),
        (Lane_sol_s05_j5.arrayLaw (I := ht.hp.Loc) X H).pr (fun A =>
          n ≤ (Lane_sol_s05_centres.markingFamily (failSets X ht H P A (X.St.stateOf y.1) j)).card) ≤
            Real.exp (-4) ^ n := by
      intro y j
      have hsite : ∀ t ∈ X.St.neighbors (X.St.stateOf y.1), X.St.oneHot t ∈ X.sites ht := by
        intro t ht
        obtain ⟨a, ha⟩ := Lane_sol_s05_j5.odd_neighbors_even X y t ht
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, congrArg X.St.oneHot ha⟩
      have hU : X.p.T n ≤ (Lane_sol_s05_j5.candidates X Q (X.St.stateOf y.1) j).card := by
        obtain ⟨t, htmem⟩ := Lane_sol_s05_j5.odd_neighbors_nonempty X (by omega) y
        have hl := (hP (X.St.oneHot t) (hsite t htmem) j).1
        rw [← hlevel P (X.St.oneHot t) j] at hl
        have hTQ : X.p.T n ≤ (Q t j).card := by exact_mod_cast hTsmall'.trans hl
        apply hTQ.trans
        apply Finset.card_le_card
        intro l hl
        exact Finset.mem_biUnion.mpr ⟨t, htmem, Finset.mem_union_left _ hl⟩
      have hUupper : ((Lane_sol_s05_j5.candidates X Q (X.St.stateOf y.1) j).card : ℝ) ≤
          8 * (n : ℝ) ^ 11 := by
        have hh := Lane_sol_s05_j5.candidates_upper X Q (X.St.stateOf y.1) j (2 * ht.hp.lam)
          (by rw [hlam]; positivity) (fun t htmem k => hupper _ (hsite t htmem) k)
        convert hh using 1
        rw [hlam]
        ring
      have hpow := pow_le_pow_left₀
        (Nat.cast_nonneg (Lane_sol_s05_j5.candidates X Q (X.St.stateOf y.1) j).card) hUupper (X.p.T n)
      simp_rw [hfeq]
      refine Lane_sol_s05_j5.star_family_bound X H Q y j (cL p.pre1) (cH p.pre1) C hgood hcount hU hT' ?_
      cases hkey : X.g.roleKey (X.p.J n) y.1 with
      | inl k =>
        simp only [hkey, HiddenKey5.level, Sum.isLeft_inl, Bool.true_eq, true_and, ite_true, step3Scale]
        exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le) (Real.exp_pos _).le).trans
            (by simpa only [hXp] using (hbudget k.2.2.val).1)
      | inr k =>
        simp only [hkey, HiddenKey5.level, Sum.isLeft_inr, Bool.false_eq_true, false_and, ite_false, add_zero, step3Scale]
        exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le) (Real.exp_pos _).le).trans
            (by simpa only [hXp] using (hbudget 0).2)
    let ν := Lane_sol_s05_j5.arrayLaw (I := ht.hp.Loc) X H
    have hbad : ∀ A, ¬ Fam P A → ∃ ij : OddRole5 n × Fin (ht.hp.H + 1),
        n ≤ (Lane_sol_s05_centres.markingFamily (failSets X ht H P A (X.St.stateOf ij.1.1) ij.2)).card := by
      intro A hA
      change ¬ ∀ b j, (Lane_sol_s05_centres.markingFamily (failSets X ht H P A b j)).card < n at hA
      obtain ⟨b, hb⟩ := not_forall.mp hA
      obtain ⟨j, hj⟩ := not_forall.mp hb
      have hj' := not_lt.mp hj
      have hne : (Lane_sol_s05_centres.markingFamily (failSets X ht H P A b j)).Nonempty :=
        Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < n) hj')
      obtain ⟨S, hS⟩ := hne
      have hSF := (Lane_sol_s05_centres.markingFamily_spec (failSets X ht H P A b j)).1 hS
      unfold failSets at hSF
      obtain ⟨μ, hμ, heq⟩ := Finset.mem_image.mp hSF
      obtain ⟨hμQ, _, y, hy, _⟩ := (Finset.mem_filter.mp hμ).2
      obtain ⟨t, htmem⟩ := Lane_sol_s05_j5.odd_neighbors_nonempty X (by omega) y
      rw [hy] at htmem
      have hm := hμQ t htmem
      have hlev : ((μ t).2 : ℕ) = j ∨ ((μ t).2 : ℕ) = j + 1 := by
        rcases Finset.mem_union.mp hm with h | h
        · exact Or.inl (Finset.mem_filter.mp h).2.2.1
        · exact Or.inr (Finset.mem_filter.mp h).2.2.1
      have hlevBound := (μ t).2.isLt
      have hjH : j ≤ ht.hp.H := by omega
      refine ⟨(y, ⟨j, by omega⟩), ?_⟩
      simpa only [hy] using hj'
    have hrole : (Fintype.card (OddRole5 n) : ℝ) ≤ (2 : ℝ) ^ n := by
      have hh : Fintype.card (OddRole5 n) ≤ Fintype.card (CubeVertex n) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      have hc : Fintype.card (CubeVertex n) = 2 ^ n := by
        simp only [CubeVertex, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      rw [hc] at hh
      exact_mod_cast hh
    have htail' : (2 : ℝ) ^ n * ((ht.hp.H + 1 : ℕ) : ℝ) * Real.exp (-4) ^ n ≤
        Real.exp (-Real.sqrt n) / 3 := by
      simpa only [Nat.cast_add, Nat.cast_one, ht, canonHt, HeightChoice5.hp, hXp] using htail
    calc
      _ ≤ ν.pr (fun A => ∃ ij : OddRole5 n × Fin (ht.hp.H + 1),
          n ≤ (Lane_sol_s05_centres.markingFamily (failSets X ht H P A (X.St.stateOf ij.1.1) ij.2)).card) :=
        FinProb.pr_mono ν _ _ hbad
      _ ≤ ∑ ij : OddRole5 n × Fin (ht.hp.H + 1), ν.pr (fun A =>
          n ≤ (Lane_sol_s05_centres.markingFamily (failSets X ht H P A (X.St.stateOf ij.1.1) ij.2)).card) :=
        FinProb.pr_exists_le_sum5 ν _
      _ ≤ ∑ _ij : OddRole5 n × Fin (ht.hp.H + 1), Real.exp (-4) ^ n :=
        Finset.sum_le_sum (fun ij _ => hsingle ij.1 ij.2)
      _ = (Fintype.card (OddRole5 n) : ℝ) * ((ht.hp.H + 1 : ℕ) : ℝ) * Real.exp (-4) ^ n := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_mul, mul_assoc]
      _ ≤ (2 : ℝ) ^ n * ((ht.hp.H + 1 : ℕ) : ℝ) * Real.exp (-4) ^ n :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrole (Nat.cast_nonneg _))
          (pow_nonneg (Real.exp_pos _).le n)
      _ ≤ _ := htail'
  let P₀ := FinProb.bernoulli (ht.hp.lam / (ht.hp.V : ℝ))
  let A₀ := FinProb.bernoulli ((n : ℝ) ^ ht.b₀ / ht.hp.lam)
  let T₀ := FinProb.uniformAll (Ω := ht.hp.TiePerm) ⟨1⟩
  let B₀ := Lane_sol_s05_j5.bundleLaw X H
  have hrest : ∀ P : ht.hp.Loc → Bool,
      (FinProb.pi fun _ : ht.hp.Loc => A₀.prod (T₀.prod B₀)).pr
        (fun W => Ball P ∧ ¬ Fam P (fun c => (W c.1).2.2 c.2)) ≤ Real.exp (-Real.sqrt n) / 3 := by
    intro P
    by_cases hB : Ball P
    · simp only [hB, true_and]
      rw [Lane_sol_s05_j5.pi_snd_pr (fun _ : ht.hp.Loc => A₀) (fun _ => T₀.prod B₀)
        (fun W => ¬ Fam P (fun c => (W c.1).2 c.2))]
      rw [Lane_sol_s05_j5.pi_snd_pr (fun _ : ht.hp.Loc => T₀) (fun _ => B₀)
        (fun W => ¬ Fam P (fun c => W c.1 c.2))]
      have hh := hcond P hB
      rw [Lane_sol_s05_j5.bundle_pr X H (fun A => ¬ Fam P A)] at hh
      simpa only [B₀, Lane_sol_s05_j5.bundleEquiv, Equiv.coe_fn_symm_mk] using hh
    · simp only [hB, false_and, FinProb.pr, if_false, Finset.sum_const_zero]
      exact div_nonneg (Real.exp_pos _).le (by norm_num)
  change (FinProb.pi fun _ : ht.hp.Loc => P₀.prod (A₀.prod (T₀.prod B₀))).pr
    (fun ω => Ball (fun l => (ω l).1) ∧ ¬ Fam (fun l => (ω l).1) (fun c => (ω c.1).2.2.2 c.2)) ≤ _
  exact Lane_sol_s05_j5.pi_pair_bound (fun _ : ht.hp.Loc => P₀)
    (fun _ => A₀.prod (T₀.prod B₀))
    (fun P W => Ball P ∧ ¬ Fam P (fun c => (W c.1).2.2 c.2))
    (Real.exp (-Real.sqrt n) / 3) hrest

/-- SUB-LEMMA J6 (05:846–849, deterministic): with correct counts, small singleton losses and
fewer than `n` failures per star, marks remove `O(n^2 T)` IDs per site-level and the eligible
sets keep `λ/3` IDs. -/
theorem legal_of_events : ∀ p : Params5 γ K' χ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ (H : X.KeyHist) (ω : X.CΩ (canonHt X)), BallsOK X (canonHt X) ω → SinglesOK X (canonHt X) H ω →
        FamiliesOK X (canonHt X) H ω →
          (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω) (X.sites (canonHt X)) := by
  sorry

/-- SUB-LEMMA J7 (05:851–855, D3.8/L3.8 applied): on legal eligibility, the long height rule
gives good heights with probability `1 - o(1)`. -/
theorem heights_tail : ∀ p : Params5 γ K' χ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ H : X.KeyHist, (X.centreLaw (canonHt X) H).pr (fun ω =>
        (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω) (X.sites (canonHt X)) ∧
          ¬ (canonHt X).hp.GoodHeights (X.sites (canonHt X)) (pos ω) (act ω)
            (markElig X (canonHt X) H ω)) ≤ 1 / 300 := by
  classical
  intro p
  obtain ⟨c, hc, nHeight, hHeight⟩ :=
    height_selection_global 10 (p.alpha / 10000) (p.alpha / 2000)
      (p.alpha / 1000000) (p.alpha / 100000) (1 - p.alpha / 100000)
      (p.alpha / 20000) (1 / 2) 2 8
      (Lane_sol_s05_centres.height_admissible p)
      (Lane_sol_s05_centres.heightRegime p)
  obtain ⟨nGeom, hGeom⟩ :=
    Filter.eventually_atTop.1 (Lane_sol_s05_centres.height_regime_eventually p)
  have hpow : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ (1 + c)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hexp : Filter.Tendsto (fun m : ℕ => Real.exp (-((m : ℝ) ^ (1 + c)))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hpow
  obtain ⟨nExp, hExp⟩ := Filter.eventually_atTop.1
    (hexp.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 300)))
  let n₀ := max nHeight (max nGeom nExp)
  refine ⟨n₀, ?_⟩
  intro n hn N E G Y hY H
  let ht := canonHt Y
  let hp := ht.hp
  have hgeom := hGeom n (by omega) (Y.p.m n) (Y.p.J n) Y.g Y.St
  have hdimlo : (1 / 2 : ℝ) * hp.n ≤ hp.d := by
    change (1 / 2 : ℝ) * n ≤ Y.St.d
    exact hgeom.1
  have hdimhi : (hp.d : ℝ) ≤ 2 * hp.n := by
    change (Y.St.d : ℝ) ≤ 2 * n
    exact hgeom.2.1
  have hreg : (Lane_sol_s05_centres.heightRegime p).ok hp.n hp.d hp.r := by
    simpa [hp, ht, canonHt, HeightChoice5.hp, hY] using hgeom.2.2
  have hscale : hp.H = topScale hp.n (p.alpha / 1000000) (p.alpha / 100000) := by
    simp [hp, ht, canonHt, HeightChoice5.hp, hY]
  have hlam : hp.lam = (hp.n : ℝ) ^ (10 : ℝ) := by
    simp [hp, HeightChoice5.hp]
  have hb₀ : hp.b₀ = p.alpha / 10000 := by
    simp [hp, ht, canonHt, HeightChoice5.hp, hY]
  have hb : hp.b = p.alpha / 2000 := by
    simp [hp, ht, canonHt, HeightChoice5.hp, hY]
  have hnHeight : nHeight ≤ n := by omega
  have hbad := hHeight hp (by simp [hp, HeightChoice5.hp]) hscale hlam hb₀ hb
    (by simpa [hp, ht, canonHt, HeightChoice5.hp] using hnHeight) hdimlo hdimhi hreg
  let Arr := ∀ K : Y.Ty, Y.Array K
  let Aux := ∀ l : hp.Loc, hp.TiePerm × Arr
  let arrayLaw : FinProb Arr :=
    FinProb.pi fun K => FinProb.pi fun _ : Fin (Y.p.typeBlocks n K) => Y.blockLaw H K
  let auxLaw : FinProb Aux :=
    FinProb.pi fun _ =>
      (FinProb.uniformAll (Ω := hp.TiePerm) ⟨1⟩).prod arrayLaw
  let posLaw : FinProb (hp.Loc → Bool) :=
    FinProb.pi fun _ => FinProb.bernoulli (hp.lam / (hp.V : ℝ))
  let actLaw : FinProb (hp.Loc → Bool) :=
    FinProb.pi fun _ => FinProb.bernoulli ((n : ℝ) ^ hp.b₀ / hp.lam)
  let law : FinProb (((hp.Loc → Bool) × Aux) × (hp.Loc → Bool)) :=
    (posLaw.prod auxLaw).prod actLaw
  let AOf : Aux → Y.ArraysOn hp.Loc := fun a q => (a q.1).2 q.2
  let Esel : (hp.Loc → Bool) → Aux → hp.EligMap :=
    fun P a => eligOf Y ht H P (AOf a)
  let e : Y.CΩ ht ≃ (((hp.Loc → Bool) × Aux) × (hp.Loc → Bool)) :=
    { toFun := fun ω =>
        ((pos ω, fun l => ((ω l).2.2.1, (ω l).2.2.2)), act ω)
      invFun := fun q l =>
        (q.1.1 l, q.2 l, (q.1.2 l).1, (q.1.2 l).2)
      left_inv := by
        intro ω
        funext l
        cases h : ω l with
        | mk a b => cases b with
          | mk b c => cases c with
            | mk c d => simp [pos, act, h]
      right_inv := by
        rintro ⟨⟨P, a⟩, A⟩
        apply Prod.ext
        · apply Prod.ext
          · rfl
          · funext l
            rfl
        · rfl }
  have prod_move (f g h : hp.Loc → ℝ) :
      (∏ l, f l * (g l * h l)) = (∏ l, f l) * (∏ l, h l) * (∏ l, g l) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ac_rfl
  have hw (ω : Y.CΩ ht) : law.w (e ω) = (Y.centreLaw ht H).w ω := by
    change law.w ((pos ω, fun l => ((ω l).2.2.1, (ω l).2.2.2)), act ω) =
      (Y.centreLaw ht H).w ω
    simp only [law, posLaw, auxLaw, actLaw, arrayLaw, Setup5.centreLaw, FinProb.prod,
      FinProb.pi, pos, act]
    exact (prod_move
      (fun l => (FinProb.bernoulli (hp.lam / (hp.V : ℝ))).w (pos ω l))
      (fun l => (FinProb.bernoulli ((n : ℝ) ^ hp.b₀ / hp.lam)).w (act ω l))
      (fun l => (FinProb.uniformAll (Ω := hp.TiePerm) ⟨1⟩).w ((ω l).2.2.1) *
        arrayLaw.w (fun K => (ω l).2.2.2 K))).symm
  let bad : (((hp.Loc → Bool) × Aux) × (hp.Loc → Bool)) → Prop := fun q =>
    hp.Legal q.1.1 (Esel q.1.1 q.1.2) (Y.sites ht) ∧
      ¬ hp.GoodHeights (Y.sites ht) q.1.1 q.2 (Esel q.1.1 q.1.2)
  let target : Y.CΩ ht → Prop := fun ω =>
    hp.Legal (pos ω) (markElig Y ht H ω) (Y.sites ht) ∧
      ¬ hp.GoodHeights (Y.sites ht) (pos ω) (act ω) (markElig Y ht H ω)
  have hAuxArr (ω : Y.CΩ ht) :
      (fun q : hp.Loc × Y.Ty => (ω q.1).2.2.2 q.2) = arraysOf ω := by
    funext q
    rfl
  have hEvent (ω : Y.CΩ ht) : bad (e ω) = target ω := by
    change bad ((pos ω, fun l => ((ω l).2.2.1, (ω l).2.2.2)), act ω) = target ω
    simp only [bad, target, Esel, AOf, markElig, pos, act]
    rw [hAuxArr ω]
  have hPred : (fun ω => bad (e ω)) = target := by
    funext ω
    exact hEvent ω
  have hpr : law.pr bad = (Y.centreLaw ht H).pr target := by
    rw [Lane_sol_s05_h1.pr_equiv (Y.centreLaw ht H) law e hw bad]
    rw [hPred]
  have htail : (Y.centreLaw ht H).pr target ≤ Real.exp (-((n : ℝ) ^ (1 + c))) := by
    exact hpr.symm ▸ hbad (Y.sites ht) auxLaw Esel
  have hnExp : nExp ≤ n := by omega
  have hexpSmall : Real.exp (-((n : ℝ) ^ (1 + c))) < 1 / 300 := hExp n hnExp
  exact htail.trans hexpSmall.le

/-- SUB-LEMMA J8 (05:874–879): raw block support, true path support and the true-target gate
at actual long records hold with probability `1 - o(1)` at good histories. -/
theorem support_tail : ∀ (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
          (X.centreLaw (canonHt X) H).pr (fun ω => ¬ SupportOK X (canonHt X) H ω) ≤ 1 / 300 := by
  classical
  intro cL cH hc
  refine ⟨Lane_sol_s05_centres.loadRequest, ?_⟩
  intro p hreq
  refine ⟨0, ?_⟩
  intro n hn N E G Y hY H hgood
  let ht := canonHt Y
  let hp := ht.hp
  let Arr := ∀ K : Y.Ty, Y.Array K
  let arrLaw : FinProb Arr :=
    FinProb.pi fun K => FinProb.pi fun _ : Fin (Y.p.typeBlocks n K) => Y.blockLaw H K
  let locLaw : FinProb (Y.CVal ht) :=
    (FinProb.bernoulli (hp.lam / (hp.V : ℝ))).prod
      ((FinProb.bernoulli ((n : ℝ) ^ hp.b₀ / hp.lam)).prod
        ((FinProb.uniformAll (Ω := hp.TiePerm) ⟨1⟩).prod arrLaw))
  have hcover := (L5_1e_cover Y.g (Y.p.J n)).2
  have hBounds : ∀ K, Y.TypeOccurs K → Y.Step2Bounds H K := by
    intro K hK
    exact Setup5.L5_1d_bounds n N E G Y hcover H hgood.base_support hgood.step1 K hK
      (hgood.step2.1 K hK)
  have hmassLower (K : Y.Ty) (hK : Y.TypeOccurs K) :
      Real.exp (-(Y.p.delta * (Y.p.q0 * Y.p.typeSegs n K)) *
        ∑ ℓ ∈ K.2.1, (colLen5 (Y.p.s n) ℓ : ℝ)) ≤ Y.blockMass H K K.2.1 := by
    have hgate := Lane_q_s05_hist1b.blockGate_trueBlock_of_step1Pass Y H K hK hgood.step1
    have hnot := hgood.step2.1 K hK
    by_contra hlt
    exact hnot ⟨hgate, Or.inl (lt_of_not_ge hlt)⟩
  have hmassPos (K : Y.Ty) (hK : Y.TypeOccurs K) : 0 < Y.blockMass H K K.2.1 :=
    (Real.exp_pos _).trans_le (hmassLower K hK)
  have hblockLawDiv (K : Y.Ty) (hK : Y.TypeOccurs K) (z : Y.Block K) :
      (Y.blockLaw H K).w z = Y.blockWeight H K K.2.1 z / Y.blockMass H K K.2.1 := by
    simpa [Setup5.blockLaw, Setup5.blockLawOn, Setup5.blockMass] using
      (Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg
        (f := fun z => Y.blockWeight H K K.2.1 z) (Y.fallbackBlock K) z
        (fun z => Lane_q_s05_hist1b.blockWeight_nonneg Y H K K.2.1 z)
        (by simpa [Setup5.blockMass] using hmassPos K hK))
  have hrawExists (K : Y.Ty) (hK : Y.TypeOccurs K) :
      ∃ z, Y.blockWeight H K K.2.1 z ≠ 0 := by
    have hpos : 0 < (Y.blockLaw H K).pr (fun _ => True) := by
      simp [FinProb.pr, (Y.blockLaw H K).sum_eq_one]
    obtain ⟨z, hz, _⟩ := FinProb.exists_support_of_pos5 (Y.blockLaw H K) (fun _ => True) hpos
    refine ⟨z, ?_⟩
    rw [hblockLawDiv K hK z] at hz
    exact (div_ne_zero_iff.mp hz).1
  have hdelMassPos (K : Y.Ty) (hK : Y.TypeOccurs K) (ℓ : Y.Key) (hℓ : ℓ ∈ K.2.1) :
      0 < Y.blockMass H K (K.2.1.erase ℓ) := by
    obtain ⟨z, hz⟩ := hrawExists K hK
    have hprodRaw := hz
    unfold Setup5.blockWeight at hprodRaw
    have hbaseGate : Y.blockBase H.1 K z *
        (if Y.blockGate H.1 K z then 1 else 0) ≠ 0 := (mul_ne_zero_iff.mp hprodRaw).1
    have hkeyProd : (∏ k ∈ K.2.1, Y.colLik H.1 K k z (H.2 k)) ≠ 0 :=
      (mul_ne_zero_iff.mp hprodRaw).2
    have hdelProd : (∏ k ∈ K.2.1.erase ℓ, Y.colLik H.1 K k z (H.2 k)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      exact (Finset.prod_ne_zero_iff.mp hkeyProd) k (Finset.mem_of_mem_erase hk)
    have hdelRaw : Y.blockWeight H K (K.2.1.erase ℓ) z ≠ 0 := by
      simpa [Setup5.blockWeight] using mul_ne_zero hbaseGate hdelProd
    have hdelNonneg := Lane_q_s05_hist1b.blockWeight_nonneg Y H K (K.2.1.erase ℓ) z
    have hdelPos : 0 < Y.blockWeight H K (K.2.1.erase ℓ) z :=
      lt_of_le_of_ne hdelNonneg (Ne.symm hdelRaw)
    have hsum : Y.blockWeight H K (K.2.1.erase ℓ) z ≤
        Y.blockMass H K (K.2.1.erase ℓ) := by
      unfold Setup5.blockMass
      exact Finset.single_le_sum
        (fun z' _ => Lane_q_s05_hist1b.blockWeight_nonneg Y H K (K.2.1.erase ℓ) z')
        (Finset.mem_univ z)
    exact lt_of_lt_of_le hdelPos hsum
  have harrayBlock (ω : Y.CΩ ht) (hω : (Y.centreLaw ht H).w ω ≠ 0)
      (l : hp.Loc) (K : Y.Ty) (i : Fin (Y.p.typeBlocks n K)) :
      (Y.blockLaw H K).w ((ω l).2.2.2 K i) ≠ 0 := by
    have hpi : (∏ l : hp.Loc, locLaw.w (ω l)) ≠ 0 := by
      change (FinProb.pi (fun _ : hp.Loc => locLaw)).w ω ≠ 0
      change (∏ l : hp.Loc, locLaw.w (ω l)) ≠ 0 at hω
      exact hω
    have hloc := (Finset.prod_ne_zero_iff.mp hpi) l (Finset.mem_univ _)
    have hloc' :
        (FinProb.bernoulli (hp.lam / (hp.V : ℝ))).w ((ω l).1) *
          ((FinProb.bernoulli ((n : ℝ) ^ hp.b₀ / hp.lam)).w ((ω l).2.1) *
            ((FinProb.uniformAll (Ω := hp.TiePerm) ⟨1⟩).w ((ω l).2.2.1) *
              arrLaw.w ((ω l).2.2.2))) ≠ 0 := by
      simpa only [locLaw, FinProb.prod] using hloc
    have hact := (mul_ne_zero_iff.mp hloc').2
    have htie := (mul_ne_zero_iff.mp hact).2
    have harr := (mul_ne_zero_iff.mp htie).2
    have hKprod :
        (∏ K : Y.Ty,
          (FinProb.pi (fun j : Fin (Y.p.typeBlocks n K) => Y.blockLaw H K)).w
            ((ω l).2.2.2 K)) ≠ 0 := by
      change arrLaw.w ((ω l).2.2.2) ≠ 0 at harr
      exact harr
    have hIprod := (Finset.prod_ne_zero_iff.mp hKprod) K (Finset.mem_univ _)
    have hIprod' :
        (∏ j : Fin (Y.p.typeBlocks n K), (Y.blockLaw H K).w ((ω l).2.2.2 K j)) ≠ 0 := by
      change (FinProb.pi (fun j : Fin (Y.p.typeBlocks n K) => Y.blockLaw H K)).w
          ((ω l).2.2.2 K) ≠ 0 at hIprod
      exact hIprod
    exact (Finset.prod_ne_zero_iff.mp hIprod') i (Finset.mem_univ _)
  have htypeOfRecord (ω : Y.CΩ ht) (y : OddRole5 n)
      (c : hp.Loc × Y.Ty) (hc : c ∈
        (Y.actualRecordAt (markElig Y ht H) H ω hp.Rlong y).2.1) : Y.TypeOccurs c.2 := by
    change c ∈ (evenNbrs y).biUnion (fun a =>
      match Y.selAt (markElig Y ht H) ω hp.Rlong a with
      | some l => {(l, Y.g.evenType (Y.p.J n) a.1)}
      | none => ∅) at hc
    obtain ⟨a, ha, hc⟩ := Finset.mem_biUnion.mp hc
    cases hs : Y.selAt (markElig Y ht H) ω hp.Rlong a with
    | none => simp [hs] at hc
    | some l =>
        have heq : c = (l, Y.g.evenType (Y.p.J n) a.1) := by simpa [hs] using hc
        cases heq
        exact ⟨a.1, a.2, rfl⟩
  have hselectedMem (ω : Y.CΩ ht) (s : CubeVertex hp.d) (l : hp.Loc)
      (hsel : hp.selection (Y.sites ht) (pos ω) (act ω) (markElig Y ht H ω)
        (tie ω) s = some l) : l ∈ markElig Y ht H ω s l.2 := by
    classical
    let j := hp.height (Y.sites ht) (pos ω) (act ω) (markElig Y ht H ω) hp.Rlong s
    change (if hj : j < hp.H then
        let j' : Fin (hp.H + 1) := ⟨j, by omega⟩
        if hbad : hp.Bad (pos ω) (act ω) (markElig Y ht H ω) s j' then none
        else
          let active := ((markElig Y ht H ω) s j').filter (fun q => act ω q = true)
          let priorities := active.image (hp.priority (tie ω) (s, j'))
          if hne : priorities.Nonempty then
            let q := priorities.min' hne
            have hq : q ∈ priorities := Finset.min'_mem priorities hne
            have hmem : ∃ z, z ∈ active ∧ hp.priority (tie ω) (s, j') z = q :=
              Finset.mem_image.mp hq
            some (Classical.choose hmem)
          else none
      else none) = some l at hsel
    by_cases hj : j < hp.H
    · rw [dif_pos hj] at hsel
      let j' : Fin (hp.H + 1) := ⟨j, by omega⟩
      change (if hbad : hp.Bad (pos ω) (act ω) (markElig Y ht H ω) s j' then none
        else
          let active := ((markElig Y ht H ω) s j').filter (fun q => act ω q = true)
          let priorities := active.image (hp.priority (tie ω) (s, j'))
          if hne : priorities.Nonempty then
            let q := priorities.min' hne
            have hq : q ∈ priorities := Finset.min'_mem priorities hne
            have hmem : ∃ z, z ∈ active ∧ hp.priority (tie ω) (s, j') z = q :=
              Finset.mem_image.mp hq
            some (Classical.choose hmem)
          else none) = some l at hsel
      by_cases hbad : hp.Bad (pos ω) (act ω) (markElig Y ht H ω) s j'
      · rw [dif_pos hbad] at hsel
        cases hsel
      · rw [dif_neg hbad] at hsel
        let active := ((markElig Y ht H ω) s j').filter (fun q => act ω q = true)
        let priorities := active.image (hp.priority (tie ω) (s, j'))
        change (if hne : priorities.Nonempty then
            let q := priorities.min' hne
            have hq : q ∈ priorities := Finset.min'_mem priorities hne
            have hmem : ∃ z, z ∈ active ∧ hp.priority (tie ω) (s, j') z = q :=
              Finset.mem_image.mp hq
            some (Classical.choose hmem)
          else none) = some l at hsel
        by_cases hne : priorities.Nonempty
        · rw [dif_pos hne] at hsel
          have hchosen := Option.some.inj hsel
          let q := priorities.min' hne
          have hq : q ∈ priorities := Finset.min'_mem priorities hne
          have hmem : ∃ z, z ∈ active ∧ hp.priority (tie ω) (s, j') z = q :=
            Finset.mem_image.mp hq
          have hmem' := Classical.choose_spec hmem
          rw [hchosen] at hmem'
          have helig : l ∈ markElig Y ht H ω s j' := (Finset.mem_filter.mp hmem'.1).1
          have hlevel : l.2 = j' := (markElig_shape Y ht H ω s j' l helig).2.1
          rw [hlevel]
          exact helig
        · rw [dif_neg hne] at hsel
          cases hsel
    · rw [dif_neg hj] at hsel
      cases hsel
  have hgoodAtSupport (ω : Y.CΩ ht) (hω : (Y.centreLaw ht H).w ω ≠ 0) :
      SupportOK Y ht H ω := by
    intro y hsel
    let r := Y.actualRecordAt (markElig Y ht H) H ω hp.Rlong y
    have hType (c : hp.Loc × Y.Ty) (hc : c ∈ r.2.1) : Y.TypeOccurs c.2 :=
      htypeOfRecord ω y c (by simpa [r] using hc)
    have hRaw (c : hp.Loc × Y.Ty) (hc : c ∈ r.2.1) (i : Fin (Y.p.typeBlocks n c.2)) :
        Y.blockWeight H c.2 c.2.2.1 (arraysOf ω c i) ≠ 0 := by
      have hK := hType c hc
      have hb := harrayBlock ω hω c.1 c.2 i
      have hb' : (Y.blockLaw H c.2).w (arraysOf ω c i) ≠ 0 := by
        simpa [Setup5.arraysOf, Setup5.arr] using hb
      have hLaw := hblockLawDiv c.2 hK (arraysOf ω c i)
      rw [hLaw] at hb'
      exact (div_ne_zero_iff.mp hb').1
    have hCandidate :
        Y.candGateOn H r (arraysOf ω) (H.2 (Y.g.roleKey (Y.p.J n) y.1)) := by
      unfold Setup5.candGateOn
      refine ⟨?_, ?_⟩
      · intro c hc hℓ
        have hK := hType c hc
        have hratioFull : Real.exp
            (-(Y.p.delta * (Y.p.q0 * Y.p.typeSegs n c.2)) * colLen5 (Y.p.s n) r.1) *
            Y.blockMass H c.2 (c.2.2.1.erase r.1) ≤
          Y.blockMass H c.2 c.2.2.1 := by
          have hnot := hgood.step2.1 c.2 hK
          have hGate := Lane_q_s05_hist1b.blockGate_trueBlock_of_step1Pass
            Y H c.2 hK hgood.step1
          have hnotRatio : ¬ Y.blockMass H c.2 c.2.2.1 <
              Real.exp (-(Y.p.delta * (Y.p.q0 * Y.p.typeSegs n c.2)) * colLen5 (Y.p.s n) r.1) *
                Y.blockMass H c.2 (c.2.2.1.erase r.1) := by
            intro hlt
            exact hnot ⟨hGate, Or.inr ⟨r.1, hℓ, hlt⟩⟩
          exact le_of_not_gt hnotRatio
        have hwithCol : Y.withCol H r.1 (H.2 r.1) = H := by
          cases r.1 <;> simp [Setup5.withCol]
        have hratio : Real.exp
              (-(Y.p.delta * (Y.p.q0 * Y.p.typeSegs n c.2)) * colLen5 (Y.p.s n) r.1) *
              Y.blockMass H c.2 (c.2.2.1.erase r.1) ≤
            Y.blockMass (Y.withCol H r.1 (H.2 r.1)) c.2 c.2.2.1 := by
          rw [hwithCol]
          exact hratioFull
        refine ⟨hdelMassPos c.2 hK r.1 hℓ, ?_⟩
        exact hratio
      · intro c M hmask h
        -- The mask in an actual record is selected from a high pool; its entries
        -- either list the true key or pass the singleton optional-hit test.
        have hmaskSpec :
            ∃ k, Y.g.roleKey (Y.p.J n) y.1 = .inl k ∧
              ∃ a : EvenRole5 n, a ∈ evenNbrs y ∧
                (Y.g.evenType (Y.p.J n) a.1).2.2 = none ∧
                Y.selAt (markElig Y ht H) ω hp.Rlong a = some c.1 ∧
                c.2 = Y.g.evenType (Y.p.J n) a.1 ∧
                M = Y.firstK (Y.hitSet (arraysOf ω) (c.1, c.2)
                  (Y.lowCol H.2 k)) (Y.p.usedBlocks n) := by
          cases hrole : Y.g.roleKey (Y.p.J n) y.1 with
          | inr kH =>
              simp [r, Setup5.actualRecordAt, hrole] at hmask
          | inl k =>
              have hm := hmask
              simp only [r, Setup5.actualRecordAt, hrole] at hm
              by_cases hex : ∃ a : EvenRole5 n, a ∈ evenNbrs y ∧
                  (Y.g.evenType (Y.p.J n) a.1).2.2 = none ∧
                    (Y.selAt (markElig Y ht H) ω hp.Rlong a).isSome
              · rw [dif_pos hex] at hm
                let a := Classical.choose hex
                have ha := Classical.choose_spec hex
                cases hs : Y.selAt (markElig Y ht H) ω hp.Rlong a with
                | none => rw [hs] at hm; cases hm
                | some l =>
                    rw [hs] at hm
                    have htuple :
                        (l, Y.g.evenType (Y.p.J n) a.1,
                          Y.firstK (Y.hitSet (arraysOf ω)
                            (l, Y.g.evenType (Y.p.J n) a.1) (Y.lowCol H.2 k))
                            (Y.p.usedBlocks n)) = (c.1, c.2, M) :=
                      Option.some.inj hm
                    rcases Prod.mk.inj htuple with ⟨hl, hrest⟩
                    rcases Prod.mk.inj hrest with ⟨hK, hM⟩
                    have hselOut : Y.selAt (markElig Y ht H) ω hp.Rlong a = some c.1 := by
                      rw [hs, hl]
                    have hMout : M = Y.firstK (Y.hitSet (arraysOf ω) (c.1, c.2)
                        (Y.lowCol H.2 k)) (Y.p.usedBlocks n) := by
                      simpa [hl, hK] using hM.symm
                    exact ⟨k, rfl, a, ha.1, ha.2.1, hselOut, hK.symm, hMout⟩
              · rw [dif_neg hex] at hm
                cases hm
        rcases hmaskSpec with ⟨k, hrole, a, ha, hmode, hselA, hK, hM⟩
        have hroleKey : r.1 = (.inl k : Y.Key) := by
          simpa [r, Setup5.actualRecordAt] using hrole
        have htargetEq : H.2 r.1 h = Y.lowCol H.2 k := by
          let Fibre : Y.Key → Type := fun ℓ => Fin (colLen5 (Y.p.s n) ℓ)
          let h' : Fibre (.inl k) :=
            Eq.recOn hroleKey h
          have hpair : (⟨r.1, h⟩ : Σ ℓ : Y.Key, Fibre ℓ) = ⟨.inl k, h'⟩ := by
            apply Sigma.ext hroleKey
            exact (eqRec_heq (φ := Fibre) hroleKey h).symm
          have heq : H.2 r.1 h = H.2 (.inl k) h' :=
            congrArg (fun z : Σ ℓ : Y.Key, Fibre ℓ => H.2 z.1 z.2) hpair
          have hlen : colLen5 (Y.p.s n) (.inl k : Y.Key) = 1 := rfl
          have h0 : h' = (⟨0, by norm_num⟩ : Fin 1) := by
            apply Fin.ext
            have hlt : (h'.val : ℕ) < 1 := by
              simpa only [colLen5] using h'.isLt
            omega
          rw [heq, h0]
          apply congrArg (H.2 (.inl k))
          apply Fin.ext
          rfl
        have hselected :
            c.1 ∈ markElig Y ht H ω (Y.siteOf a) c.1.2 := by
          have hselHP : hp.selection (Y.sites ht) (pos ω) (act ω)
              (markElig Y ht H ω) (tie ω) (Y.siteOf a) = some c.1 := by
            simpa [Setup5.selAt, Setup5.siteOf, HDParams.selection] using hselA
          exact hselectedMem ω (Y.siteOf a) c.1 hselHP
        have hsingleton : singletonOK Y ht H (arraysOf ω) a c.1 := by
          have hmem : c.1 ∈ eligOf Y ht H (pos ω) (arraysOf ω)
              (Y.siteOf a) c.1.2 := hselected
          simp only [eligOf, Finset.mem_filter] at hmem
          exact hmem.2.1 a rfl
        have hhit : Y.p.usedBlocks n ≤
            (Y.hitSet (arraysOf ω) (c.1, c.2) (H.2 r.1 h)).card := by
          have hadj : (cube n).Adj a.1 y.1 := (Finset.mem_filter.mp ha).2
          rcases (L5_1e_cover Y.g (Y.p.J n)).1 a.1 y.1 hadj with hlisted | hopt
          · have hobs : c ∈ r.2.1 := by
              change c ∈ (evenNbrs y).biUnion (fun b =>
                match Y.selAt (markElig Y ht H) ω hp.Rlong b with
                | some q => {(q, Y.g.evenType (Y.p.J n) b.1)}
                | none => ∅)
              apply Finset.mem_biUnion.mpr
              refine ⟨a, ha, ?_⟩
              rw [hselA]
              change c ∈ {(c.1, Y.g.evenType (Y.p.J n) a.1)}
              exact Finset.mem_singleton.mpr (Prod.ext rfl hK)
            have hTypeK : Y.TypeOccurs c.2 := hType c hobs
            have hlistedK : r.1 ∈ c.2.2.1 := by
              have hlisted' := hlisted
              rw [hrole] at hlisted'
              rw [hroleKey, hK]
              exact hlisted'
            have hpoolSub : Y.poolIdx ⊆
                Y.hitSet (arraysOf ω) (c.1, c.2) (H.2 r.1 h) := by
              intro i hi
              have hiPool : (i : ℕ) < Y.p.poolBlocks n := by
                simpa [Setup5.poolIdx] using (Finset.mem_filter.mp hi).2
              have htypeBlocks : Y.p.typeBlocks n c.2 = Y.p.poolBlocks n := by
                rw [hK]
                simp [Params5.typeBlocks, hmode]
              have hiType : (i : ℕ) < Y.p.typeBlocks n c.2 := by
                simpa [htypeBlocks] using hiPool
              let i' : Fin (Y.p.typeBlocks n c.2) := ⟨i, hiType⟩
              have hidx : Y.blockIdx c.2 i = some i' := by
                simp [Setup5.blockIdx, i', hiType]
              have hblock := harrayBlock ω hω c.1 c.2 i'
              have hhitBlock := (hBounds c.2 hTypeK).2.2
                (arraysOf ω (c.1, c.2) i') hblock r.1 hlistedK h
              unfold Setup5.hitSet
              simp only [Finset.mem_filter]
              exact ⟨hi, ⟨i', hidx, hhitBlock⟩⟩
            have hcard := Finset.card_le_card hpoolSub
            have hpoolIdxCard : Y.poolIdx.card = Y.p.poolBlocks n := by
              have hb : Y.p.poolBlocks n ≤ Y.blockBound := le_max_left _ _
              unfold Setup5.poolIdx
              rw [Fin.card_filter_val_lt, Nat.min_eq_right hb]
            calc
              Y.p.usedBlocks n ≤ Y.p.poolBlocks n :=
                Lane_sol_s05_centres.usedBlocks_le_pool Y
              _ = Y.poolIdx.card := hpoolIdxCard.symm
              _ ≤ (Y.hitSet (arraysOf ω) (c.1, c.2) (H.2 r.1 h)).card := hcard
          · have hopt' : Y.g.optionalKey (Y.p.J n) a.1 = some (.inl k) := by
              simpa [hrole] using hopt
            have hhitLow := hsingleton.2 k hopt'
            have hcardEq := congrArg (fun z =>
              (Y.hitSet (arraysOf ω) (c.1, c.2) z).card) htargetEq
            rw [hcardEq]
            simpa [hK] using hhitLow
        refine ⟨hhit, ?_⟩
        rw [hM]
        exact congrArg (fun z => Y.firstK (Y.hitSet (arraysOf ω) (c.1, c.2) z)
          (Y.p.usedBlocks n)) htargetEq
    have hPost : 0 < Y.step3PostOn H r (arraysOf ω) none (H.2 r.1) := by
      let θ₀ := H.2 r.1
      have hpriorEach (j : Fin (colLen5 (Y.p.s n) r.1)) :
          0 < (Y.prior H.1 r.1).w (θ₀ j) :=
        lt_of_le_of_ne ((Y.prior H.1 r.1).nonneg (θ₀ j))
          (Ne.symm (hgood.key_support r.1 j))
      have hpriorPos : 0 < ∏ j, (Y.prior H.1 r.1).w (θ₀ j) :=
        Finset.prod_pos fun j _ => hpriorEach j
      have hwithColTrue : Y.withCol H r.1 θ₀ = H := by
        apply Prod.ext
        · rfl
        · funext ℓ
          simp [Setup5.withCol, θ₀]
      have hobsPos : 0 < Y.obsLikOn H r (arraysOf ω) θ₀ none := by
        unfold Setup5.obsLikOn
        apply Finset.prod_pos
        intro c hc
        apply Finset.prod_pos
        intro i _
        have hcMem : c ∈ r.2.1 := (Finset.mem_filter.mp hc).1
        have hℓ : r.1 ∈ c.2.2.1 := (Finset.mem_filter.mp hc).2
        have hTypeK : Y.TypeOccurs c.2 := hType c hcMem
        have hdelMass := hdelMassPos c.2 hTypeK r.1 hℓ
        have hrawFull := hRaw c hcMem i
        have hrawExpand := hrawFull
        unfold Setup5.blockWeight at hrawExpand
        have hcommon : Y.blockBase H.1 c.2 (arraysOf ω c i) *
            (if Y.blockGate H.1 c.2 (arraysOf ω c i) then 1 else 0) ≠ 0 :=
          (mul_ne_zero_iff.mp hrawExpand).1
        have hkeyProd : (∏ k ∈ c.2.2.1,
            Y.colLik H.1 c.2 k (arraysOf ω c i) (H.2 k)) ≠ 0 :=
          (mul_ne_zero_iff.mp hrawExpand).2
        have hdelProd : (∏ k ∈ c.2.2.1.erase r.1,
            Y.colLik H.1 c.2 k (arraysOf ω c i) (H.2 k)) ≠ 0 := by
          apply Finset.prod_ne_zero_iff.mpr
          intro k hk
          exact (Finset.prod_ne_zero_iff.mp hkeyProd) k
            (Finset.mem_of_mem_erase hk)
        have hdelRaw : Y.blockWeight H c.2 (c.2.2.1.erase r.1)
            (arraysOf ω c i) ≠ 0 := by
          simpa [Setup5.blockWeight] using mul_ne_zero hcommon hdelProd
        have hdelDiv : (Y.blockLawDel H c.2 r.1).w (arraysOf ω c i) =
            Y.blockWeight H c.2 (c.2.2.1.erase r.1) (arraysOf ω c i) /
              Y.blockMass H c.2 (c.2.2.1.erase r.1) := by
          simpa [Setup5.blockLawDel, Setup5.blockLawOn, Setup5.blockMass] using
            (Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg
              (f := fun z => Y.blockWeight H c.2 (c.2.2.1.erase r.1) z)
              (Y.fallbackBlock c.2) (arraysOf ω c i)
              (fun z => Lane_q_s05_hist1b.blockWeight_nonneg Y H c.2
                (c.2.2.1.erase r.1) z) hdelMass)
        have hdenLaw : (Y.blockLawDel H c.2 r.1).w (arraysOf ω c i) ≠ 0 := by
          rw [hdelDiv]
          exact div_ne_zero hdelRaw (ne_of_gt hdelMass)
        have hnumLawBase : (Y.blockLaw H c.2).w (arraysOf ω c i) ≠ 0 := by
          rw [hblockLawDiv c.2 hTypeK]
          exact div_ne_zero hrawFull (ne_of_gt (hmassPos c.2 hTypeK))
        have hnumLaw : (Y.blockLaw (Y.withCol H r.1 θ₀) c.2).w
            (arraysOf ω c i) ≠ 0 := by
          rw [hwithColTrue]
          exact hnumLawBase
        have hnumPos : 0 < (Y.blockLaw (Y.withCol H r.1 θ₀) c.2).w
            (arraysOf ω c i) :=
          lt_of_le_of_ne ((Y.blockLaw (Y.withCol H r.1 θ₀) c.2).nonneg
            (arraysOf ω c i))
            (Ne.symm hnumLaw)
        have hdenPos : 0 < (Y.blockLawDel H c.2 r.1).w (arraysOf ω c i) :=
          lt_of_le_of_ne ((Y.blockLawDel H c.2 r.1).nonneg (arraysOf ω c i))
            (Ne.symm hdenLaw)
        have hratioPos : 0 < ratio5
            ((Y.blockLaw (Y.withCol H r.1 θ₀) c.2).w (arraysOf ω c i))
            ((Y.blockLawDel H c.2 r.1).w (arraysOf ω c i)) := by
          by_cases hz : (Y.blockLawDel H c.2 r.1).w (arraysOf ω c i) = 0
          · exact (ne_of_gt hdenPos) hz |>.elim
          · simp [ratio5, hz]
            exact div_pos hnumPos hdenPos
        have hnotRef : ¬ Y.InRef (none : Option
            (hp.Loc × Y.Ty × Finset (Fin Y.blockBound))) c i := by
          simp [Setup5.InRef]
        rw [if_neg hnotRef]
        exact hratioPos
      have hgate : Y.candGateOn H r (arraysOf ω) θ₀ := by
        change Y.candGateOn H r (arraysOf ω)
          (H.2 (Y.g.roleKey (Y.p.J n) y.1))
        exact hCandidate
      have hnumPos : 0 <
          (∏ j, (Y.prior H.1 r.1).w (θ₀ j)) *
            (if Y.candGateOn H r (arraysOf ω) θ₀ then 1 else 0) *
            Y.obsLikOn H r (arraysOf ω) θ₀ none := by
        rw [if_pos hgate]
        exact mul_pos (mul_pos hpriorPos one_pos) hobsPos
      have hmassPos : 0 < Y.step3MassOn H r (arraysOf ω) none := by
        unfold Setup5.step3MassOn
        let f : (Fin (colLen5 (Y.p.s n) r.1) → Fin N) → ℝ := fun θ =>
          (∏ j, (Y.prior H.1 r.1).w (θ j)) *
            (if Y.candGateOn H r (arraysOf ω) θ then 1 else 0) *
            Y.obsLikOn H r (arraysOf ω) θ none
        have hterm : 0 < f θ₀ := by simpa [f] using hnumPos
        apply lt_of_lt_of_le hterm
        exact Finset.single_le_sum
          (f := f)
          (fun θ _ => by
            apply mul_nonneg
            · apply mul_nonneg
              · exact Finset.prod_nonneg fun j _ =>
                  (Y.prior H.1 r.1).nonneg _
              · split_ifs <;> norm_num
            · exact Lane_sol_s05_hist1b.obsLikOn_nonneg Y H r (arraysOf ω) θ none)
          (Finset.mem_univ θ₀)
      unfold Setup5.step3PostOn
      exact div_pos hnumPos hmassPos
    exact ⟨hRaw, hPost, hCandidate⟩
  have hprobZero : (Y.centreLaw ht H).pr (fun ω => ¬ SupportOK Y ht H ω) = 0 := by
    unfold FinProb.pr
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hω : (Y.centreLaw ht H).w ω = 0
    · simp [hω]
    · have hgoodω := hgoodAtSupport ω hω
      have hnotEvent : ¬ (¬ SupportOK Y ht H ω) := by
        intro hbad
        exact hbad hgoodω
      simp [hnotEvent]
  rw [hprobZero]
  norm_num

set_option maxHeartbeats 8000000 in
/-- SUB-LEMMA J9 (05:851–860, deterministic): good heights give a choice everywhere on two
consecutive levels around each odd state, the crowd bound gives at most `2n^b ≤ T` IDs, the
singleton tests give hits and heavy fractions, and maximality (`markElig_sound`) gives Step 3. -/
theorem success_of_events : ∀ p : Params5 γ K' χ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ (H : X.KeyHist) (ω : X.CΩ (canonHt X)), X.baseLaw.w H.1 ≠ 0 → X.Step1Pass H.1 →
        (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω) (X.sites (canonHt X)) →
        BallsOK X (canonHt X) ω →
        (canonHt X).hp.GoodHeights (X.sites (canonHt X)) (pos ω) (act ω) (markElig X (canonHt X) H ω) →
        SupportOK X (canonHt X) H ω → CentreSuccess X (canonHt X) H ω := by
  classical
  intro p
  have hpow0 : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ (n : ℝ) ^ (p.alpha / 2000) :=
    ((tendsto_rpow_atTop (by have := p.halpha.1; positivity : (0 : ℝ) < p.alpha / 2000)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hpow : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n ∧ 2 ≤ (n : ℝ) ^ (p.alpha / 2000) := by
    filter_upwards [hpow0, Filter.eventually_ge_atTop (1 : ℕ)] with n h1 h2
    exact ⟨h2, h1⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hpow
  refine ⟨n₀, ?_⟩
  intro n hn N E G X hXp H ω hbase hstep1 hlegal hballs hgood hsupp
  let ht := canonHt X
  let Sites := X.sites ht
  let elig := markElig X ht H ω
  let eligFn := markElig X ht H
  let P := pos ω
  let A := act ω
  let τ := tie ω
  let hp := ht.hp
  have hn1 : 1 ≤ n := (hn₀ n hn).1
  have hnpos : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsmallT : 2 * (n : ℝ) ^ hp.b ≤ (X.p.T n : ℝ) := by
    have hnFacts := hn₀ n hn
    have hbasePow : 2 ≤ (n : ℝ) ^ (p.alpha / 2000) := hnFacts.2
    have hdouble : 2 * (n : ℝ) ^ (p.alpha / 2000) ≤
        (n : ℝ) ^ (p.alpha / 1000) := by
      have hexp : p.alpha / 1000 = p.alpha / 2000 + p.alpha / 2000 := by ring
      rw [hexp, Real.rpow_add (by exact_mod_cast hnpos)]
      exact mul_le_mul_of_nonneg_right hbasePow
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)) _)
    have hceil : (p.m n : ℝ) ^ (1 / 1000 : ℝ) ≤ (p.T n : ℝ) := Nat.le_ceil _
    have hm : (n : ℝ) ^ p.alpha ≤ (p.m n : ℝ) := by
      exact_mod_cast (Nat.le_ceil ((n : ℝ) ^ p.alpha))
    have hmono := Real.rpow_le_rpow (by positivity) hm (by norm_num : (0 : ℝ) ≤ 1 / 1000)
    have heq : ((n : ℝ) ^ p.alpha) ^ (1 / 1000 : ℝ) =
        (n : ℝ) ^ (p.alpha / 1000) := by
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (n : ℝ))]
      congr 1
      ring
    have hb : hp.b = p.alpha / 2000 := by
      change X.p.alpha / 2000 = p.alpha / 2000
      rw [hXp]
    have hceilX : (p.m n : ℝ) ^ (1 / 1000 : ℝ) ≤ (X.p.T n : ℝ) := by
      simpa [hXp] using hceil
    rw [hb]
    calc
      2 * (n : ℝ) ^ (p.alpha / 2000) ≤ (n : ℝ) ^ (p.alpha / 1000) := hdouble
      _ = ((n : ℝ) ^ p.alpha) ^ (1 / 1000 : ℝ) := heq.symm
      _ ≤ (p.m n : ℝ) ^ (1 / 1000 : ℝ) := hmono
      _ ≤ (X.p.T n : ℝ) := hceilX
  have hsitesGood : hp.GoodHeights Sites P A elig →
      ∀ s ∈ Sites, hp.selection Sites P A elig τ s |>.isSome := by
    intro hg s hs
    have hprops := hg s hs
    have hheight : hp.height Sites P A elig hp.Rlong s < hp.H := hprops.1
    have hbad : ¬ hp.Bad P A elig s ⟨hp.height Sites P A elig hp.Rlong s,
        Nat.lt_succ_of_le hheight.le⟩ := by
      intro hb
      exact hprops.2.1 ⟨Nat.lt_succ_of_le hheight.le, hb⟩
    have hactive : ∃ l ∈ elig s ⟨hp.height Sites P A elig hp.Rlong s,
        Nat.lt_succ_of_le hheight.le⟩, A l = true := by
      by_contra hnone
      apply hbad
      left
      intro l hl
      by_cases ha : A l = true
      · exact (hnone ⟨l, hl, ha⟩).elim
      · cases hv : A l <;> simp_all
    have hactive' : (elig s ⟨hp.height Sites P A elig hp.Rlong s,
        Nat.lt_succ_of_le hheight.le⟩).filter
        (fun l => A l = true) |>.Nonempty := by
      rcases hactive with ⟨l, hl, ha⟩
      exact ⟨l, Finset.mem_filter.mpr ⟨hl, ha⟩⟩
    have hprior : (((elig s ⟨hp.height Sites P A elig hp.Rlong s,
        Nat.lt_succ_of_le hheight.le⟩).filter
        (fun l => A l = true)).image (hp.priority τ (s,
          ⟨hp.height Sites P A elig hp.Rlong s, Nat.lt_succ_of_le hheight.le⟩))).Nonempty := by
      exact hactive'.image _
    simpa [HDParams.selection, HDParams.selectionAt, hheight, hbad, hprior]
  have hselected_spec (s : CubeVertex hp.d) (j : ℕ) (hj : j < hp.H)
      (hheight : hp.height Sites P A elig hp.Rlong s = j)
      (hbad : ¬ hp.Bad P A elig s ⟨j, Nat.lt_succ_of_le hj.le⟩) (l : hp.Loc)
      (hsel : hp.selection Sites P A elig τ s = some l) :
      l ∈ elig s ⟨j, Nat.lt_succ_of_le hj.le⟩ ∧ A l = true := by
    classical
    simp [HDParams.selection, HDParams.selectionAt, hheight, hj, hbad] at hsel
    let j' : Fin (hp.H + 1) := ⟨j, Nat.lt_succ_of_le hj.le⟩
    let active : Finset hp.Loc := (elig s j').filter (fun x => A x = true)
    let priorities := active.image (hp.priority τ (s, j'))
    have hneP : priorities.Nonempty := by
      rcases hsel.1 with ⟨x, hx⟩
      exact ⟨hp.priority τ (s, j') x, Finset.mem_image.mpr ⟨x, by simpa [active, j'] using hx, rfl⟩⟩
    let q := priorities.min' hneP
    have hmem : ∃ x, x ∈ active ∧ hp.priority τ (s, j') x = q :=
      Finset.mem_image.mp (Finset.min'_mem priorities hneP)
    have hchosen : Classical.choose hmem = l := by
      simpa [active, priorities, q, j'] using hsel.2
    rcases Classical.choose_spec hmem with ⟨hactive, _⟩
    rw [hchosen] at hactive
    have hactive' : l ∈ (elig s j').filter (fun x => A x = true) := by
      simpa [active] using hactive
    exact Finset.mem_filter.mp hactive'
  have hshape_of_selection (s : CubeVertex hp.d) (j : ℕ) (hj : j < hp.H)
      (hheight : hp.height Sites P A elig hp.Rlong s = j)
      (hbad : ¬ hp.Bad P A elig s ⟨j, Nat.lt_succ_of_le hj.le⟩) (l : hp.Loc)
      (hsel : hp.selection Sites P A elig τ s = some l) :
      P l = true ∧ l.2 = ⟨j, Nat.lt_succ_of_le hj.le⟩ ∧ hammingDist l.1 s ≤ hp.r := by
    have hmem := (hselected_spec s j hj hheight hbad l hsel).1
    rcases Lane_opus_s05.markElig_shape X ht H ω s
        ⟨j, Nat.lt_succ_of_le hj.le⟩ l hmem with ⟨hP, hlev, hdist⟩
    exact ⟨by simpa [P] using hP, hlev, hdist⟩
  have hselect_at (s : CubeVertex hp.d) (hs : s ∈ Sites) :
      ∃ l, hp.selection Sites P A elig τ s = some l := by
    have hs' := hsitesGood hgood s hs
    cases hsel : hp.selection Sites P A elig τ s with
    | none => simp [hsel] at hs'
    | some l => exact ⟨l, rfl⟩
  have hlegal' : hp.Legal P elig Sites := by simpa [hp, P, elig, Sites, ht] using hlegal
  have hglobal : ∀ v : EvenRole5 n, (X.selLong (markElig X ht H) ω v).isSome := by
    intro v
    have hv : X.siteOf v ∈ Sites := by
      apply Finset.mem_image.mpr
      exact ⟨v, Finset.mem_univ _, rfl⟩
    have hs := hsitesGood hgood (X.siteOf v) hv
    change (hp.selection Sites P A elig τ (X.siteOf v)).isSome = true
    exact hs
  have hstar : ∀ (y : OddRole5 n), LocalValidAt X ht (markElig X ht) H ω hp.Rlong y := by
    intro y
    let b := X.St.stateOf y.1
    let S := X.St.neighbors b
    let heightAt : X.St.Site → ℕ := fun t => hp.height Sites P A elig hp.Rlong (X.St.oneHot t)
    have adj_flip {x z : CubeVertex n} (hAdj : (cube n).Adj x z) :
        ∃ i : Fin n, x = flipVertex5 z i := by
      classical
      have hc : (Finset.univ.filter fun i : Fin n => x i ≠ z i).card = 1 := hAdj
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
      refine ⟨i, ?_⟩
      funext k
      by_cases hki : k = i
      · subst k
        have hmem : i ∈ Finset.univ.filter (fun j : Fin n => x j ≠ z j) := by
          rw [hi]
          simp
        have hne : x i ≠ z i := (Finset.mem_filter.mp hmem).2
        cases hx : x i <;> cases hz : z i <;> simp_all [flipVertex5]
      · have heq : x k = z k := by
          by_contra hne
          have hmem : k ∈ Finset.univ.filter (fun j : Fin n => x j ≠ z j) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
          rw [hi] at hmem
          exact hki (Finset.mem_singleton.mp hmem)
        simp [flipVertex5, hki, heq]
    have neigh_even (t : X.St.Site) (htS : t ∈ S) :
        ∃ x : CubeVertex n, X.St.stateOf x = t ∧ IsEvenRole x := by
      obtain ⟨x, z, hx, hz, hAdj⟩ := (X.St.mem_neighbors b t).mp htS
      have hxOdd : ¬ IsEvenRole x := by
        have hpar := (X.St.state_determines x y.1 hx).2.2.2.1
        intro he
        exact y.2 (hpar.mp he)
      have hflip : IsEvenRole z := by
        have hpar : IsEvenRole x ↔ ¬ IsEvenRole z := by
          obtain ⟨i, hi⟩ := adj_flip hAdj
          rw [hi]
          simpa [flipVertex5, cubeFlip] using (cubeFlip_parity z i)
        by_contra hzEven
        exact hxOdd (hpar.mpr hzEven)
      exact ⟨z, hz, hflip⟩
    have site_mem (t : X.St.Site) (htS : t ∈ S) : X.St.oneHot t ∈ Sites := by
      obtain ⟨x, hx, hEven⟩ := neigh_even t htS
      apply Finset.mem_image.mpr
      exact ⟨⟨x, hEven⟩, Finset.mem_univ _, by simp [Setup5.siteOf, hx]⟩
    have hSnon : S.Nonempty := by
      let i : Fin n := ⟨0, by omega⟩
      refine ⟨X.St.stateOf (cubeFlip y.1 i), ?_⟩
      apply (X.St.mem_neighbors b _).2
      exact ⟨y.1, cubeFlip y.1 i, rfl, rfl, cubeFlip_adj y.1 i⟩
    have hheight_lt (t : X.St.Site) (htS : t ∈ S) : heightAt t < hp.H :=
      (hgood (X.St.oneHot t) (site_mem t htS)).1
    have hnotbad (t : X.St.Site) (htS : t ∈ S) :
        ¬ hp.Bad P A elig (X.St.oneHot t)
          ⟨heightAt t, Nat.lt_succ_of_le (hheight_lt t htS).le⟩ := by
      intro hb'
      exact (hgood (X.St.oneHot t) (site_mem t htS)).2.1
        ⟨Nat.lt_succ_of_le (hheight_lt t htS).le, hb'⟩
    have hselect_some (t : X.St.Site) (htS : t ∈ S) :
        ∃ l, hp.selection Sites P A elig τ (X.St.oneHot t) = some l :=
      hselect_at (X.St.oneHot t) (site_mem t htS)
    let μ : X.St.Site → hp.Loc := fun t =>
      if htS : t ∈ S then Classical.choose (hselect_some t htS) else default
    have hμsel (t : X.St.Site) (htS : t ∈ S) :
        hp.selection Sites P A elig τ (X.St.oneHot t) = some (μ t) := by
      dsimp only [μ]
      rw [dif_pos htS]
      exact Classical.choose_spec (hselect_some t htS)
    have hμshape (t : X.St.Site) (htS : t ∈ S) :
        P (μ t) = true ∧ (μ t).2 = ⟨heightAt t,
          Nat.lt_succ_of_le (hheight_lt t htS).le⟩ ∧
          hammingDist (μ t).1 (X.St.oneHot t) ≤ hp.r := by
      exact hshape_of_selection (X.St.oneHot t) (heightAt t) (hheight_lt t htS) rfl
        (hnotbad t htS) (μ t) (hμsel t htS)
    have hμactive (t : X.St.Site) (htS : t ∈ S) : A (μ t) = true := by
      exact (hselected_spec (X.St.oneHot t) (heightAt t) (hheight_lt t htS) rfl
        (hnotbad t htS) (μ t) (hμsel t htS)).2
    have hdist (t t' : X.St.Site) (htS : t ∈ S) (htS' : t' ∈ S) :
        _root_.hammingDist (X.St.oneHot t) (X.St.oneHot t') ≤ 8 := by
      exact X.St.even_distance b t t' htS htS' (neigh_even t htS) (neigh_even t' htS')
    let heights := S.image heightAt
    have hheights_nonempty : heights.Nonempty := by
      rcases hSnon with ⟨t, htS⟩
      exact ⟨heightAt t, Finset.mem_image.mpr ⟨t, htS, rfl⟩⟩
    let j := heights.min' hheights_nonempty
    have hj_mem : j ∈ heights := Finset.min'_mem heights hheights_nonempty
    obtain ⟨t₀, ht₀S, ht₀j⟩ := Finset.mem_image.mp hj_mem
    have hj_le (t : X.St.Site) (htS : t ∈ S) : j ≤ heightAt t :=
      Finset.min'_le heights (heightAt t) (Finset.mem_image.mpr ⟨t, htS, rfl⟩)
    have hlevel (t : X.St.Site) (htS : t ∈ S) : heightAt t = j ∨ heightAt t = j + 1 := by
      have hclose := (hgood (X.St.oneHot t₀) (site_mem t₀ ht₀S)).2.2
        (X.St.oneHot t) (site_mem t htS) (hdist t₀ t ht₀S htS)
      change |(heightAt t₀ : ℤ) - (heightAt t : ℤ)| ≤ 1 at hclose
      rw [ht₀j] at hclose
      have hbounds := abs_le.mp hclose
      have hupper : (heightAt t : ℤ) ≤ (j : ℤ) + 1 := by omega
      have hupperNat : heightAt t ≤ j + 1 := by exact_mod_cast hupper
      by_cases hEq : heightAt t = j
      · exact Or.inl hEq
      · right
        have hlt : j < heightAt t := lt_of_le_of_ne (hj_le t htS) (Ne.symm hEq)
        exact le_antisymm hupperNat (Nat.succ_le_of_lt hlt)
    have hj_lt : j < hp.H := by
      have := hheight_lt t₀ ht₀S
      omega
    let jfin : Fin (hp.H + 1) := ⟨j, Nat.lt_succ_of_le hj_lt.le⟩
    let M := S.image μ
    let M₀ := M.filter fun l => l.2.val = j
    let M₁ := M.filter fun l => l.2.val = j + 1
    have hM_levels (l : hp.Loc) (hl : l ∈ M) : l.2.val = j ∨ l.2.val = j + 1 := by
      obtain ⟨t, htS, rfl⟩ := Finset.mem_image.mp hl
      have hr := hlevel t htS
      have hμval := congrArg Fin.val (hμshape t htS).2.1
      simp only [Fin.val_mk] at hμval
      rcases hr with hr | hr <;> simp [hr, hμval]
    have hM_eq : M = M₀ ∪ M₁ := by
      ext l
      constructor
      · intro hl
        rcases hM_levels l hl with h | h
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hl, h⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hl, h⟩))
      · intro hl
        rcases Finset.mem_union.mp hl with hl | hl
        · exact (Finset.mem_filter.mp hl).1
        · exact (Finset.mem_filter.mp hl).1
    have hgroup_bound (k : ℕ) (t₀ : X.St.Site) (ht₀S : t₀ ∈ S)
        (hcenter : heightAt t₀ = k) (hk : k < hp.H)
        (Mk : Finset hp.Loc) (hMk : Mk ⊆ M)
        (hMk_level : ∀ l ∈ Mk, l.2.val = k) : (Mk.card : ℝ) ≤ (n : ℝ) ^ hp.b := by
      let kfin : Fin (hp.H + 1) := ⟨k, Nat.lt_succ_of_le hk.le⟩
      let Ck : Finset (CubeVertex hp.d) := Finset.univ.filter fun u =>
        P (u, kfin) = true ∧ A (u, kfin) = true ∧
          _root_.hammingDist u (X.St.oneHot t₀) ≤ hp.r + hp.D
      have hnot : ¬ hp.Bad P A elig (X.St.oneHot t₀) kfin := by
        have hn := hnotbad t₀ ht₀S
        have heq : (⟨heightAt t₀, Nat.lt_succ_of_le (hheight_lt t₀ ht₀S).le⟩ :
            Fin (hp.H + 1)) = kfin := by
          exact Fin.ext (by simp [hcenter, kfin])
        simpa [heq] using hn
      have hnotCrowd : ¬ (n : ℝ) ^ hp.b < (Ck.card : ℝ) := by
        have hnC : ¬ (hp.n : ℝ) ^ hp.b < (Ck.card : ℝ) := by
          have hnBad : ¬ ((∀ l ∈ elig (X.St.oneHot t₀) kfin, A l = false) ∨
              (hp.n : ℝ) ^ hp.b <
                ((Finset.univ.filter (fun u : CubeVertex hp.d =>
                  P (u, kfin) = true ∧ A (u, kfin) = true ∧
                    _root_.hammingDist u (X.St.oneHot t₀) ≤ hp.r + hp.D)).card : ℝ)) := by
            simpa only [HDParams.Bad] using hnot
          exact (not_or.mp hnBad).2
        simpa [hp, ht, canonHt, HeightChoice5.hp, Ck, P, A, kfin] using hnC
      have hCk : (Ck.card : ℝ) ≤ (n : ℝ) ^ hp.b := not_lt.mp hnotCrowd
      let locs := Mk.image Prod.fst
      have hloc_subset : locs ⊆ Ck := by
        intro u hu
        obtain ⟨z, hz, hzu⟩ := Finset.mem_image.mp hu
        obtain ⟨t, htS, htz⟩ := Finset.mem_image.mp (hMk hz)
        have hshape := hμshape t htS
        have hactive := hμactive t htS
        have hlev : (μ t).2.val = k := by
          rw [htz]
          exact hMk_level z hz
        have hfin : (μ t).2 = kfin := Fin.ext hlev
        have hpair : z = (u, kfin) := by
          apply Prod.ext
          · exact hzu
          · have hlevZ : z.2.val = k := by
              rw [htz] at hlev
              exact hlev
            exact Fin.ext hlevZ
        have hμpair : μ t = (u, kfin) := htz.trans hpair
        have hdist' : _root_.hammingDist u (X.St.oneHot t₀) ≤ hp.r + hp.D := by
          have htDist := hdist t t₀ htS ht₀S
          have htri := _root_.hammingDist_triangle u (X.St.oneHot t) (X.St.oneHot t₀)
          have hrShape : _root_.hammingDist (μ t).1 (X.St.oneHot t) ≤ hp.r := by
            simpa [HypercubeRamsey.hammingDist, _root_.hammingDist] using hshape.2.2
          have hloc : (μ t).1 = u := by
            have h := congrArg Prod.fst hμpair
            simpa using h
          have hr : _root_.hammingDist u (X.St.oneHot t) ≤ hp.r := by
            rw [← hloc]
            exact hrShape
          have hD : hp.D = 8 := by simp [hp, ht, canonHt, HeightChoice5.hp]
          have htDist' : _root_.hammingDist (X.St.oneHot t) (X.St.oneHot t₀) ≤ hp.D := by
            omega
          calc
            _ ≤ _ := htri
            _ ≤ hp.r + hp.D := Nat.add_le_add hr htDist'
        have hP : P (u, kfin) = true := by
          simpa [hμpair] using hshape.1
        have hA : A (u, kfin) = true := by
          simpa [hμpair] using hactive
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP, hA, hdist'⟩
      have hinj : Set.InjOn Prod.fst (↑Mk : Set hp.Loc) := by
        intro l hl l' hl' hfst
        change l ∈ Mk at hl
        change l' ∈ Mk at hl'
        obtain ⟨u, i⟩ := l
        obtain ⟨u', i'⟩ := l'
        simp only [Prod.fst] at hfst
        subst u'
        have hi : i.val = k := hMk_level (u, i) hl
        have hi' : i'.val = k := hMk_level (u, i') hl'
        have : i = i' := Fin.ext (by omega)
        subst i'
        rfl
      have hcard_image : locs.card = Mk.card := Finset.card_image_iff.mpr hinj
      have hcard : Mk.card ≤ Ck.card := by
        rw [← hcard_image]
        exact Finset.card_le_card hloc_subset
      have hcardR : (Mk.card : ℝ) ≤ (Ck.card : ℝ) := by exact_mod_cast hcard
      exact hcardR.trans hCk
    have hM₀_bound : (M₀.card : ℝ) ≤ (n : ℝ) ^ hp.b := by
      exact hgroup_bound j t₀ ht₀S ht₀j hj_lt M₀ (by
        intro l hl
        exact (Finset.mem_filter.mp hl).1) (by
        intro l hl
        exact (Finset.mem_filter.mp hl).2)
    have hM₁_bound : (M₁.card : ℝ) ≤ (n : ℝ) ^ hp.b := by
      by_cases hne : M₁.Nonempty
      · obtain ⟨l, hl⟩ := hne
        obtain ⟨t, htS, htl⟩ := Finset.mem_image.mp
          ((Finset.mem_filter.mp hl).1)
        have hlevel_t : heightAt t = j + 1 := by
          have hval := congrArg Fin.val (hμshape t htS).2.1
          have hmk := (Finset.mem_filter.mp hl).2
          rw [← htl] at hmk
          simp only [Fin.val_mk] at hval
          omega
        exact hgroup_bound (j + 1) t htS hlevel_t (by
          have := hheight_lt t htS
          omega) M₁ (by
          intro l' hl'
          exact (Finset.mem_filter.mp hl').1) (by
          intro l' hl'
          exact (Finset.mem_filter.mp hl').2)
      · have hempty : M₁ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        simp [hempty]
        positivity
    have hMcard : (M.card : ℝ) ≤ 2 * (n : ℝ) ^ hp.b := by
      have hcard : M.card ≤ M₀.card + M₁.card := by
        rw [hM_eq]
        exact Finset.card_union_le M₀ M₁
      calc
        (M.card : ℝ) ≤ (M₀.card : ℝ) + (M₁.card : ℝ) := by exact_mod_cast hcard
        _ ≤ 2 * (n : ℝ) ^ hp.b := by linarith [hM₀_bound, hM₁_bound]
    have hT : M.card ≤ X.p.T n := by
      exact_mod_cast hMcard.trans hsmallT
    have hsiteState (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
        X.St.stateOf a.1 ∈ S := by
      apply (X.St.mem_neighbors b _).2
      exact ⟨y.1, a.1, rfl, rfl, (cube n).adj_symm (Finset.mem_filter.mp ha).2⟩
    have hsel_at (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
        X.selAt eligFn ω hp.Rlong a = some (μ (X.St.stateOf a.1)) := by
      change hp.selectionAt Sites P A elig τ hp.Rlong (X.siteOf a) =
        some (μ (X.St.stateOf a.1))
      simpa [HDParams.selection, Setup5.siteOf] using hμsel (X.St.stateOf a.1) (hsiteState a ha)
    have hμelig (t : X.St.Site) (htS : t ∈ S) : μ t ∈ elig (X.St.oneHot t) (μ t).2 := by
      have hmem := (hselected_spec (X.St.oneHot t) (heightAt t) (hheight_lt t htS) rfl
        (hnotbad t htS) (μ t) (hμsel t htS)).1
      rw [(hμshape t htS).2.1]
      exact hmem
    have hμsingleton (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
        Lane_opus_s05.singletonOK X ht H (arraysOf ω) a (μ (X.St.stateOf a.1)) := by
      have htS := hsiteState a ha
      have hm := hμelig (X.St.stateOf a.1) htS
      change μ (X.St.stateOf a.1) ∈ Lane_opus_s05.eligOf X ht H (pos ω) (arraysOf ω)
        (X.St.oneHot (X.St.stateOf a.1)) (μ (X.St.stateOf a.1)).2 at hm
      simp only [Lane_opus_s05.eligOf, Finset.mem_filter] at hm
      rcases hm with ⟨_, hprop⟩
      exact hprop.1 a (by rfl)
    have hlevels : ∀ t ∈ S, (μ t).2.val = j ∨ (μ t).2.val = j + 1 := by
      intro t htS
      have hval := congrArg Fin.val (hμshape t htS).2.1
      simp only [Fin.val_mk] at hval
      simpa [hval] using hlevel t htS
    have hT' : ((evenNbrs y).image fun a => X.selAt eligFn ω hp.Rlong a).card ≤ X.p.T n := by
      let ids := (evenNbrs y).image fun a => μ (X.St.stateOf a.1)
      let opts := ids.image (fun l => some l)
      have hselImg : (evenNbrs y).image (fun a => X.selAt eligFn ω hp.Rlong a) = opts := by
        calc
          _ = (evenNbrs y).image (fun a => some (μ (X.St.stateOf a.1))) := by
            apply Finset.image_congr
            intro a ha
            exact hsel_at a ha
          _ = opts := by
            dsimp [opts, ids]
            rw [Finset.image_image]
            rfl
      have hinj : Set.InjOn (fun l : hp.Loc => some l) (↑ids : Set hp.Loc) := by
        intro l hl l' hl' heq
        exact Option.some.inj heq
      have hopts : opts.card = ids.card := Finset.card_image_iff.mpr hinj
      have hids : ids ⊆ M := by
        intro l hl
        obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hl
        have hm : μ (X.St.stateOf a.1) ∈ S.image μ :=
          Finset.mem_image.mpr ⟨X.St.stateOf a.1, hsiteState a ha, rfl⟩
        simpa [M, ← heq] using hm
      calc
        _ = opts.card := by rw [hselImg]
        _ = ids.card := hopts
        _ ≤ M.card := Finset.card_le_card hids
        _ ≤ X.p.T n := hT
    have hlongsome (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
        (X.selLong (markElig X ht H) ω a).isSome := by
      have hs := hselect_at (X.St.oneHot (X.St.stateOf a.1))
        (site_mem (X.St.stateOf a.1) (hsiteState a ha))
      change (hp.selection Sites P A elig τ (X.siteOf a)).isSome = true
      rcases hs with ⟨l, hl⟩
      have hl' : hp.selection Sites P A elig τ (X.siteOf a) = some l := by
        simpa [Setup5.siteOf] using hl
      simp [hl']
    have hstep3 : ¬ X.step3FailOn H (X.actualRecordAt eligFn H ω hp.Rlong y) (arraysOf ω) := by
      apply Lane_opus_s05.markElig_sound X ht H ω hp.Rlong y μ j hj_lt.le
      · intro t htS
        exact hμelig t htS
      · exact hlevels
      · exact hT
      · intro a ha
        exact hsel_at a ha
    unfold LocalValidAt
    dsimp only
    refine ⟨hbase, hstep1, ?_, ?_, hT', ?_, ?_, ?_, ?_, ?_, hstep3⟩
    · intro a ha
      exact hlongsome a ha
    · intro a ha j'
      have hcount := hballs (X.St.oneHot (X.St.stateOf a.1))
        (site_mem (X.St.stateOf a.1) (hsiteState a ha)) j'
      exact hcount.2
    · intro a ha l k hsel hkey
      have heq : l = μ (X.St.stateOf a.1) :=
        Option.some.inj (hsel.symm.trans (hsel_at a ha))
      rw [heq]
      exact (hμsingleton a ha).2 k hkey
    · intro a ha l hsel
      have heq : l = μ (X.St.stateOf a.1) :=
        Option.some.inj (hsel.symm.trans (hsel_at a ha))
      rw [heq]
      have hc : X.heavyCount H ω a
          (μ (X.St.stateOf a.1), X.refSubset H ω a (μ (X.St.stateOf a.1))) =
          Lane_opus_s05.heavyCountOn X ht H (arraysOf ω) a
            (μ (X.St.stateOf a.1), X.refSubset H ω a (μ (X.St.stateOf a.1))) := by
        rfl
      rw [hc]
      exact (hμsingleton a ha).1
    · have hs := hsupp y (by intro a ha; exact hlongsome a ha)
      exact hs.1
    · have hs := hsupp y (by intro a ha; exact hlongsome a ha)
      exact hs.2.1
    · have hs := hsupp y (by intro a ha; exact hlongsome a ha)
      exact hs.2.2
  unfold Lane_opus_s05.CentreSuccess
  exact ⟨hlegal', hglobal, hstar⟩

/-- SUB-LEMMA J10 (union bound over J3–J9): the two probability estimates of L5.1j. -/
theorem markElig_estimates : ∀ (C : ℝ) (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        X.RecordCount C → ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
          (X.centreLaw (canonHt X) H).pr (fun ω =>
              ¬ (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω) (X.sites (canonHt X))) ≤
            Real.exp (-Real.sqrt n) ∧
          (X.centreLaw (canonHt X) H).pr (fun ω => ¬ CentreSuccess X (canonHt X) H ω) ≤ 1 / 100 := by
  sorry

/-- SUB-LEMMA J11 (05:880–887): local validity at the long radius reads center data within
`r + centreSlack`: neighbouring sites lie within `4√n + 302` of the odd image
(`Lane_sol_s05_centres.adjacent_embedding_upper`), selections read `Rlong + r + 16` around them
(`markElig_local`), and `centreSlack_scope` absorbs both. -/
theorem localValid_local (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (y : OddRole5 n) :
    FinProb.DependsOn (fun ω => X.LocalValidAt (canonHt X) (markElig X (canonHt X)) H ω (canonHt X).hp.Rlong y)
      (X.scopeBall (h := canonHt X) y.1 ((canonHt X).hp.r + Lane_sol_s05_centres.centreSlack X.p n)) := by
  sorry

/-- The short presentation mass for a given height choice and eligibility (as in
`shortPresentationMass`). -/
def shortPresMassOf (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (elig : X.KeyHist → X.CΩ ht → ht.hp.EligMap) (H : X.KeyHist) (y : OddRole5 n)
    (r : X.RecordOn ht.hp.Loc) (a : X.ArraysOn ht.hp.Loc) : ℝ :=
  (X.centreLaw ht H).pr fun ω =>
    X.LocalValidAt ht elig H ω (ht.hp.Rshort (X.p.m n)) y ∧
    X.actualRecordAt (elig H) H ω (ht.hp.Rshort (X.p.m n)) y = r ∧
    ∀ c ∈ r.2.1, arraysOf ω c = a c

/-- SUB-LEMMA J12 (05:991–1001): the short presentation reads low keys only at sign distance
`O(√m)`: the short tube, bounded star distances, `CubeStates5.sign_distance`, and integration of
unread arrays. -/
theorem presentation_local : ∃ Ckey : ℕ, ∀ p : Params5 γ K' χ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ b hi y r a, FinProb.DependsOn
        (fun lo => shortPresMassOf X (canonHt X) (markElig X (canonHt X)) (b, X.joinHidden hi lo) y r a)
        (Finset.univ.filter fun k : X.LowIdx =>
          hammingDist k.2.1 (X.g.sign y.1) ≤ Ckey * Nat.sqrt (X.p.m n)) := by
  sorry

/-- The centre layer built from the marking eligibility. -/
def markLayer (X : Setup5 γ K' χ n N E G)
    (hsmall : (Lane_sol_s05_centres.centreSlack X.p n : ℝ) ≤
      (n : ℝ) ^ (1 - ((canonHt X).ζ - (canonHt X).σ) / 4)) : X.CentreLayer5 where
  ht := canonHt X
  elig := markElig X (canonHt X)
  elig_preActivation := markElig_preActivation X (canonHt X)
  elig_shape := markElig_shape X (canonHt X)
  valid H ω y := X.LocalValidAt (canonHt X) (markElig X (canonHt X)) H ω (canonHt X).hp.Rlong y
  success := CentreSuccess X (canonHt X)
  slack := Lane_sol_s05_centres.centreSlack X.p n
  slack_small := hsmall
  slack_large := canonHt_slack_large X
  slack_nbr y a ha := by
    have hadj : (cube n).Adj a.1 y.1 := (Finset.mem_filter.mp ha).2
    have h1 := Lane_sol_s05_centres.adjacent_embedding_upper X.St a.1 y.1 hadj
    have h2 := Lane_sol_s05_centres.centreSlack_scope X.p n
    have hR : ((canonHt X).hp.Rlong : ℝ) =
        16 * (topScale n (X.p.alpha / 1000000) (X.p.alpha / 100000) : ℝ) := by
      simp only [HDParams.Rlong, HeightChoice5.hp, canonHt]
      push_cast
      ring
    have hle : ((hammingDist (X.siteOf a) (X.St.oneHot (X.St.stateOf y.1)) + (canonHt X).hp.Rlong + 16 : ℕ) : ℝ)
        ≤ (Lane_sol_s05_centres.centreSlack X.p n : ℝ) := by
      push_cast
      rw [hR]
      simp only [siteOf]
      linarith
    exact_mod_cast hle
  elig_local := markElig_local X (canonHt X)
  valid_local := localValid_local X
  success_valid H ω h y := h.2.2 y
  success_legal H ω h := h.1
  success_select H ω h := h.2.1
  valid_select H ω y h := h.2.2.1
  valid_base_support H ω y h := h.1
  valid_step1 H ω y h := h.2.1
  valid_block_support H ω y h := h.2.2.2.2.2.2.2.1
  valid_path_support H ω y h := h.2.2.2.2.2.2.2.2.1
  valid_counts H ω y h := h.2.2.2.1
  valid_T H ω y h := h.2.2.2.2.1
  valid_hits H ω y h := h.2.2.2.2.2.1
  valid_heavy H ω y h a ha c hc := by
    cases hs : X.selLong (markElig X (canonHt X) H) ω a with
    | none => simp [evenRefOf, hs] at hc
    | some l =>
      have hc' : c = (l, X.refSubset H ω a l) := by simpa [evenRefOf, hs] using hc.symm
      subst hc'
      exact h.2.2.2.2.2.2.1 a ha l hs
  valid_gate H ω y h := h.2.2.2.2.2.2.2.2.2.1
  valid_step3 H ω y h := h.2.2.2.2.2.2.2.2.2.2

/-- The canonical slack is eventually sublinear. -/
theorem slack_small_eventually (p : Params5 γ K' χ) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (Lane_sol_s05_centres.centreSlack p n : ℝ) ≤ (n : ℝ) ^ (1 - 9 * p.alpha / 4000000) :=
  Filter.eventually_atTop.mp (Lane_sol_s05_centres.centreSlack_small_eventually p)

theorem canonHt_gap (X : Setup5 γ K' χ n N E G) :
    1 - ((canonHt X).ζ - (canonHt X).σ) / 4 = 1 - 9 * X.p.alpha / 4000000 := by
  simp only [canonHt]
  ring

/-- L5.1j from the sub-lemmas. -/
theorem L5_1j_proof : ∀ (C : ℝ) (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ Ckey : ℕ, ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        X.RecordCount C → ∃ L : X.CentreLayer5, X.LowLayer5 L Ckey (cL p.pre1) (cH p.pre1) ∧
          ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
            (X.centreLaw L.ht H).pr (fun ω => ¬ L.success H ω) ≤ 1 / 100 := by
  intro C cL cH hc
  obtain ⟨Ckey, hkey⟩ := presentation_local (γ := γ) (K' := K') (χ := χ)
  obtain ⟨R, hR⟩ := markElig_estimates (γ := γ) (K' := K') (χ := χ) C cL cH hc
  refine ⟨Ckey, R, fun p hp => ?_⟩
  obtain ⟨n₁, h₁⟩ := hR p hp
  obtain ⟨n₂, h₂⟩ := hkey p
  obtain ⟨n₃, h₃⟩ := slack_small_eventually p
  refine ⟨max n₁ (max n₂ n₃), fun n hn N E G X hXp hRC => ?_⟩
  have hn₁ : n ≥ n₁ := le_trans (le_max_left _ _) hn
  have hn₂ : n ≥ n₂ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn₃ : n ≥ n₃ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hsmall : (Lane_sol_s05_centres.centreSlack X.p n : ℝ) ≤
      (n : ℝ) ^ (1 - ((canonHt X).ζ - (canonHt X).σ) / 4) := by
    rw [canonHt_gap X, hXp]
    exact h₃ n hn₃
  refine ⟨markLayer X hsmall, ?_, ?_⟩
  · exact
      { valid_eq := fun H ω y => Iff.rfl
        presentation_local := fun b hi y r a => h₂ n hn₂ N E G X hXp b hi y r a
        size_failure := fun H hH => (h₁ n hn₁ N E G X hXp hRC H hH).1 }
  · intro H hH
    exact (h₁ n hn₁ N E G X hXp hRC H hH).2

/-! ## L5.1k rows -/

section K

/-- The selection table and the rows it defines at every consultation radius (05:896–985).
`rowAt R` is the row computed with consultation radius `R` from the short-rule table; the
long row is `rowAt Rlong`, the proxy row `rowAt Rshort`. -/
structure LowTable5 (L : X.CentreLayer5) (Cloc : ℕ) where
  Data : X.Base → X.HighHid → OddRole5 n → Type
  dataFintype : ∀ b hi y, Fintype (Data b hi y)
  selExp : ∀ b hi y (lo : X.LowHid), @SelectionExperiment5 (Fin N) (Data b hi y) _ (dataFintype b hi y)
  selExp_prior : ∀ b hi y lo, X.g.low (X.p.J n) y.1 →
    (selExp b hi y lo).prior = X.prior b (X.g.roleKey (X.p.J n) y.1)
  selExp_records : ∀ b hi y lo, Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1))) *
    (selExp b hi y lo).recordBound ≤ 1
  rowAt : ℕ → X.KeyHist → X.CΩ L.ht → OddRole5 n → X.OddOut → ℝ
  /-- Equal neighbouring choices give equal rows (05:880–887,987–995). -/
  rowAt_congr : ∀ R R' H ω y, (∀ a ∈ evenNbrs y, X.selAt (L.elig H) ω R a = X.selAt (L.elig H) ω R' a) →
    rowAt R H ω y = rowAt R' H ω y
  rowAt_nonneg : ∀ R H ω y o, 0 ≤ rowAt R H ω y o
  rowAt_high : ∀ R H ω y o, ¬ X.g.low (X.p.J n) y.1 → rowAt R H ω y o = 0
  rowAt_cap : ∀ R H ω y o, (N : ℝ) * rowAt R H ω y o ≤ Real.exp (X.p.DL n)
  long_index : ∀ H ω y o, (o.1 : ℕ) ≠ 0 → rowAt L.ht.hp.Rlong H ω y o = 0
  long_invalid : ∀ H ω y o, ¬ L.valid H ω y → rowAt L.ht.hp.Rlong H ω y o = 0
  long_sum : ∀ H ω y, L.valid H ω y → X.g.low (X.p.J n) y.1 → ∑ o, rowAt L.ht.hp.Rlong H ω y o = 1
  long_support : ∀ H ω y o, rowAt L.ht.hp.Rlong H ω y o ≠ 0 → ∀ a ∈ evenNbrs y, ∀ c,
    X.evenRefOf (L.elig H) H ω a = some c → ∀ z ∈ X.refBlocks ω a c, X.BlockHits _ z o.2
  long_deletion : ∀ H ω y, L.valid H ω y → X.g.low (X.p.J n) y.1 →
    ∀ c ∈ X.refsOn H (X.actualRecord (L.elig H) H ω y) (arraysOf ω), ∀ o,
      rowAt L.ht.hp.Rlong H ω y o ≤ Real.exp (X.p.a 4 * X.refLen c.2.1 c.2.2) *
        X.step3PostOn H (X.actualRecord (L.elig H) H ω y) (arraysOf ω) (some c) (fun _ => o.2)
  long_local : ∀ H y, FinProb.DependsOn (fun ω => rowAt L.ht.hp.Rlong H ω y)
    (X.scopeBall (h := L.ht) y.1 (L.ht.hp.r + L.slack))
  /-- Disintegration of the target-averaged short-row mean (05:910–929,975–985). -/
  short_mean : ∀ b hi y lo x, X.g.low (X.p.J n) y.1 →
    ∑ y', (X.prior b (X.g.roleKey (X.p.J n) y.1)).w y' *
        (X.centreLaw L.ht (b, X.joinHidden hi (Function.update lo (X.lowIdxOf (X.g.roleKey (X.p.J n) y.1))
          (fun _ => y')))).expect (fun ω => (N : ℝ) * rowAt (L.ht.hp.Rshort (X.p.m n))
            (b, X.joinHidden hi (Function.update lo (X.lowIdxOf (X.g.roleKey (X.p.J n) y.1))
              (fun _ => y'))) ω y (0, x)) =
      (N : ℝ) * @Finset.sum (Data b hi y) ℝ _ (@Finset.univ _ (dataFintype b hi y)) (fun d =>
        (selExp b hi y lo).selectedMass d *
          (selExp b hi y lo).proxyRow (Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1)))) d x)
  /-- Key locality of the short-row mean (05:991–1001). -/
  short_local : ∀ b hi y x, FinProb.DependsOn
    (fun lo => (X.centreLaw L.ht (b, X.joinHidden hi lo)).expect
      (fun ω => (N : ℝ) * rowAt (L.ht.hp.Rshort (X.p.m n)) (b, X.joinHidden hi lo) ω y (0, x)))
    (Finset.univ.filter fun k : X.LowIdx =>
      hammingDist k.2.1 (X.g.sign y.1) ≤ Cloc * Nat.sqrt (X.p.m n))

attribute [instance] LowTable5.dataFintype

end K

/-- SUB-LEMMA K1 (05:896–985): the short-rule selection table, its rows at every radius, their
pointwise properties (row comparison `≤ ε⁻¹ P`, Step 3 deletion multiplier `e^{a₄ k_c}`, cap
`e^{D_L}/N`), the disintegration identity and the key locality.  The table is built at fixed
`b, hi, lo` outside the target, as in TeX 05:898–903. -/
theorem lowTable_exists : ∀ (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) → ∀ Ckey : ℕ,
    ∃ Cloc : ℕ, ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
      X.p = p → (∀ x : CubeVertex n, ∀ ℓ ∈ X.g.typeKeys (X.p.J n) x, (X.g.key x).1 ∈ binList5 ℓ.coarse) →
        ∀ L : X.CentreLayer5, X.LowLayer5 L Ckey (cL p.pre1) (cH p.pre1) →
          Nonempty (LowTable5 X L Cloc) := by
  sorry

/-- SUB-LEMMA K2 (05:987–1001): at a good history the long-row mean exceeds the short-row mean
by at most `1`: rows agree when neighbouring choices agree (`rowAt_congr`), the height lemma
bounds mismatch by `o(e^{-2m^{1/5}})` at each of `O(n)` neighbours on correct sizes
(`LowLayer5.size_failure` for the rest), and the cap is `e^{D_L}`. -/
theorem lowTable_long_vs_short : ∀ (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) → ∀ Ckey : ℕ,
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
      X.p = p → ∀ L : X.CentreLayer5, X.LowLayer5 L Ckey (cL p.pre1) (cH p.pre1) →
        ∀ (Cloc : ℕ) (T : LowTable5 X L Cloc) (H : X.KeyHist), X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
          ∀ y x, X.g.low (X.p.J n) y.1 →
            (X.centreLaw L.ht H).expect (fun ω => (N : ℝ) * T.rowAt L.ht.hp.Rlong H ω y (0, x)) ≤
              (X.centreLaw L.ht H).expect
                (fun ω => (N : ℝ) * T.rowAt (L.ht.hp.Rshort (X.p.m n)) H ω y (0, x)) + 1 := by
  sorry

theorem expect_nonneg' {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ P.expect f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (hf ω)

theorem expect_le_const {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (f : Ω → ℝ) (c : ℝ)
    (hf : ∀ ω, f ω ≤ c) : P.expect f ≤ c := by
  calc P.expect f = ∑ ω, P.w ω * f ω := rfl
    _ ≤ ∑ ω, P.w ω * c := Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hf ω) (P.nonneg ω)
    _ = c := by rw [← Finset.sum_mul, P.sum_eq_one, one_mul]

/-- The low rows from a selection table and the comparison. -/
def lowRowsOf (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (cL cH : ℝ) (Cloc : ℕ)
    (T : LowTable5 X L Cloc)
    (hcmp : ∀ H, X.KeyGood5 H cL cH → ∀ y x, X.g.low (X.p.J n) y.1 →
      (X.centreLaw L.ht H).expect (fun ω => (N : ℝ) * T.rowAt L.ht.hp.Rlong H ω y (0, x)) ≤
        (X.centreLaw L.ht H).expect
          (fun ω => (N : ℝ) * T.rowAt (L.ht.hp.Rshort (X.p.m n)) H ω y (0, x)) + 1) :
    X.LowRows5 L cL cH where
  row := T.rowAt L.ht.hp.Rlong
  proxy H y x := (X.centreLaw L.ht H).expect
    (fun ω => (N : ℝ) * T.rowAt (L.ht.hp.Rshort (X.p.m n)) H ω y (0, x))
  row_nonneg := T.rowAt_nonneg _
  row_high := T.rowAt_high _
  row_index := T.long_index
  row_invalid := T.long_invalid
  row_sum := T.long_sum
  row_cap := T.rowAt_cap _
  row_support := T.long_support
  row_deletion := T.long_deletion
  row_local := T.long_local
  long_vs_proxy := hcmp
  proxy_nonneg H y x := expect_nonneg' _ _ fun ω =>
    mul_nonneg (Nat.cast_nonneg _) (T.rowAt_nonneg _ H ω y _)
  proxy_high H y x hy := by
    simp [FinProb.expect, T.rowAt_high _ H _ y _ hy]
  proxy_cap H y x := expect_le_const _ _ _ fun ω => T.rowAt_cap _ H ω y _
  proxyRadius := Cloc
  proxy_local b hi y := by
    intro lo lo' h
    funext x
    exact T.short_local b hi y x lo lo' h
  Data := T.Data
  dataFintype := T.dataFintype
  selExp := T.selExp
  selExp_prior := T.selExp_prior
  selExp_records := T.selExp_records
  selExp_mean := T.short_mean

/-- L5.1k rows from the sub-lemmas. -/
theorem L5_1k_rows_proof : ∀ (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) → ∀ Ckey : ℕ,
    ∃ Cloc : ℕ, ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
      X.p = p → (∀ x : CubeVertex n, ∀ ℓ ∈ X.g.typeKeys (X.p.J n) x, (X.g.key x).1 ∈ binList5 ℓ.coarse) →
        ∀ L : X.CentreLayer5, X.LowLayer5 L Ckey (cL p.pre1) (cH p.pre1) →
          ∃ LR : X.LowRows5 L (cL p.pre1) (cH p.pre1), LR.proxyRadius ≤ Cloc := by
  intro cL cH hc Ckey
  obtain ⟨Cloc, R₁, h₁⟩ := lowTable_exists (γ := γ) (K' := K') (χ := χ) cL cH hc Ckey
  obtain ⟨R₂, h₂⟩ := lowTable_long_vs_short (γ := γ) (K' := K') (χ := χ) cL cH hc Ckey
  refine ⟨Cloc, R₁.join R₂, fun p hp => ?_⟩
  obtain ⟨hp₁, hp₂⟩ := ParamReq5.holds_of_join hp
  obtain ⟨n₁, hn₁⟩ := h₁ p hp₁
  obtain ⟨n₂, hn₂⟩ := h₂ p hp₂
  refine ⟨max n₁ n₂, fun n hn N E G X hXp hcov L hL => ?_⟩
  obtain ⟨T⟩ := hn₁ n (le_trans (le_max_left _ _) hn) N E G X hXp hcov L hL
  exact ⟨lowRowsOf X L _ _ Cloc T (hn₂ n (le_trans (le_max_right _ _) hn) N E G X hXp L hL Cloc T),
    le_rfl⟩

end Lane_opus_s05

/-- L5.1j (05:818–894): at every good key history the marking and singleton rules, the long height rule and
uniform ties give geometry success with probability `1 - o(1)` — balls hold `λ/2..2λ` prospective centers,
maximal families of disjoint Step 3 failures have fewer than `n` members (disjoint ID sets read independent
arrays; the history bounds and the record counts), eligible sets keep `λ/3` centers, neighbouring even states
use two consecutive levels and at most `2n^b ≤ T` IDs, and every actual mapping passes Step 3 by maximality. -/
theorem L5_1j : ∀ (C : ℝ) (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ Ckey : ℕ, ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        X.RecordCount C → ∃ L : X.CentreLayer5, X.LowLayer5 L Ckey (cL p.pre1) (cH p.pre1) ∧
          ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
            (X.centreLaw L.ht H).pr (fun ω => ¬ L.success H ω) ≤ 1 / 100 :=
  Lane_opus_s05.L5_1j_proof

/-- L5.1k, row construction (05:896–1001): the canonical records, the short-rule presentation table `a_y` (a
ratio of finite sums in the experiment with the target replaced and the unrecorded arrays regenerated at the
candidate value), the adjusted or fallback rows, the proxy means, their locality (sign distance `O(√m)`), the
long/short comparison (`o(e^{-2m^{1/5}})` mismatch at each of `O(n)` neighbouring states, cap `e^{D_L}`), and the
deletion bound `e^{a₄ k_c}` from the Step 3 bounds and the reserved selection multiplier. Its locality constant
is chosen before the parameter request and dimension threshold, uniformly over layers carrying
`LowLayer5` with the earlier short-presentation locality constant. Raw support alone does not retain
Step 1's fixed-base cap or supply the key locality and size-failure estimate. -/
theorem L5_1k_rows : ∀ (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) → ∀ Ckey : ℕ,
    ∃ Cloc : ℕ, ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
      X.p = p → (∀ x : CubeVertex n, ∀ ℓ ∈ X.g.typeKeys (X.p.J n) x, (X.g.key x).1 ∈ binList5 ℓ.coarse) →
        ∀ L : X.CentreLayer5, X.LowLayer5 L Ckey (cL p.pre1) (cH p.pre1) →
          ∃ LR : X.LowRows5 L (cL p.pre1) (cH p.pre1), LR.proxyRadius ≤ Cloc :=
  Lane_opus_s05.L5_1k_rows_proof

/-! ### The odd rows and their column sums (05:1003–1058) -/

/-- The odd row of a role: the low row at low roles, the high row at high roles. -/
def oddRow {L : X.CentreLayer5} {cL cH : ℝ} (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (y : OddRole5 n) (o : X.OddOut) : ℝ :=
  LR.row H ω y o + HR.row H ω y o

theorem oddRow_nonneg {L : X.CentreLayer5} {cL cH : ℝ} (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L) (H : X.KeyHist)
    (ω : X.CΩ L.ht) (y : OddRole5 n) (o : X.OddOut) : 0 ≤ X.oddRow LR HR H ω y o :=
  add_nonneg (LR.row_nonneg H ω y o) (HR.row_nonneg H ω y o)

theorem oddRow_sum {L : X.CentreLayer5} {cL cH : ℝ} (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L) (H : X.KeyHist)
    (ω : X.CΩ L.ht) (y : OddRole5 n) (hv : L.valid H ω y) : ∑ o, X.oddRow LR HR H ω y o = 1 := by
  unfold oddRow
  rw [Finset.sum_add_distrib]
  by_cases hlow : X.g.low (X.p.J n) y.1
  · rw [LR.row_sum H ω y hv hlow]
    simp [HR.row_low H ω y _ hlow]
  · rw [HR.row_sum H ω y hv hlow]
    simp [LR.row_high H ω y _ hlow]

/-- The odd row as a probability law (a fixed fallback at invalid roles). -/
def oddRowFP {L : X.CentreLayer5} {cL cH : ℝ} (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (y : OddRole5 n) : FinProb X.OddOut :=
  if hv : L.valid H ω y then
    { w := X.oddRow LR HR H ω y
      nonneg := X.oddRow_nonneg LR HR H ω y
      sum_eq_one := X.oddRow_sum LR HR H ω y hv }
  else FinProb.dirac5 (0, X.y₀)

/-- The odd column sums at every label are at most the clock threshold `θ₀ = 10^{-8}`. -/
def OddLoadsOK {L : X.CentreLayer5} {cL cH : ℝ} (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L) (H : X.KeyHist) (ω : X.CΩ L.ht) :
    Prop :=
  ∀ x : Fin N, ∑ y : OddRole5 n, ∑ o : X.OddOut, (if o.2 = x then X.oddRow LR HR H ω y o else 0) ≤ 1e-8

/-- L5.1l(3) (05:1043–1058): at a successful key history, under raw centers, with probability `1 - o(1)` all odd
column sums are at most `θ₀`: low rows have cap `e^{D_L}`, rows separated in residual coordinates by more than
`2(r + slack)` read disjoint center scopes, residual balls have fraction `e^{-Ω(n)}`, the comparison means are
the long means (at most the proxy means plus `o(1)`), whose averages are bounded at the history, and high rows
contribute at most `2 Pr_B(j > J) e^{D_H} = o(1)`; then `|B|/N ≤ 1/(2C₀)` with `C₀` large. -/
theorem L5_1l3 : ∀ C : ℝ, 0 < C → ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
      X.p = p → ChunkEstimates5 X.g → C₀ * 2 ^ n ≤ (N : ℝ) → N ≤ n * 2 ^ n →
        ∀ (L : X.CentreLayer5) (cL cH : ℝ) (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L) (H : X.KeyHist),
          X.KeySuccess5 H cL cH C LR.proxy →
            (X.centreLaw L.ht H).pr (fun ω => L.success H ω ∧ ¬ X.OddLoadsOK LR HR H ω) ≤ 1 / 100 := by
  classical
  intro C hC
  refine ⟨Lane_sol_s05_centres.loadRequest, ?_⟩
  intro p hp
  let B : ℝ := C + 2
  let C₀ : ℝ := 8 * B * 1e8
  have hB : 0 < B := by dsimp [B]; linarith
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀, hC₀, ?_⟩
  let q : ℝ := p.rho + 1 / 4
  let c : ℝ := Real.log 2 - Real.binEntropy q
  have hq0 : 0 ≤ q := by dsimp [q]; linarith [p.hrho.1]
  have hq : q < 1 / 2 := by dsimp [q]; linarith [p.hrho.2]
  have hc : 0 < c := by
    dsimp [c]
    exact sub_pos.mpr (Real.binEntropy_lt_log_two.mpr (by norm_num; linarith))
  have hTail : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) * (1 / 2 : ℝ) ^ n < 1 / 100 :=
    Lane_q_s05_h5l.halfPowerTail_tendsto.eventually (Iio_mem_nhds (by norm_num))
  have hEv := (Lane_sol_s05_centres.scope_radius_eventually p).and
    ((Lane_sol_s05_centres.near_cap_eventually p c hc).and
      ((Lane_sol_s05_centres.high_fraction_eventually p hp).and
        (hTail.and (Filter.eventually_ge_atTop (1 : ℕ)))))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hEv
  refine ⟨n₀, ?_⟩
  intro n hn N E G X hXp hGeom hNlo hNhi L cL cH LR HR H hH
  rcases hn₀ n hn with ⟨hRadius, hNearCap, ⟨hJ, hJm, hs, hHighTail⟩, hTailn, hn1⟩
  have hnpos : 0 < n := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Fin.pos X.y₀
  have hsX : 0 < X.p.s n := by simpa [hXp] using hs
  have hspos : (0 : ℝ) < X.p.s n := by exact_mod_cast hsX
  let μ := X.centreLaw L.ht H
  let Z : OddRole5 n → X.CΩ L.ht → Fin N → ℝ := fun y ω x =>
    (N : ℝ) * ∑ i : Fin (X.p.s n + 1), X.oddRow LR HR H ω y (i, x)
  let scope : OddRole5 n → Finset L.ht.hp.Loc := fun y =>
    X.scopeBall (h := L.ht) y.1 (L.ht.hp.r + L.slack)
  let near : OddRole5 n → Finset (OddRole5 n) := fun y =>
    Finset.univ.filter fun y' => X.g.residualDist y'.1 y.1 ≤ 2 * (L.ht.hp.r + L.slack)
  let f : ℝ := 2 * Real.exp (-c * n)
  let cap : ℝ := Real.exp (X.p.DL n) + 4 * Real.exp (X.p.DH n)
  have hLow (ω : X.CΩ L.ht) (y : OddRole5 n) (x : Fin N) :
      (∑ i : Fin (X.p.s n + 1), LR.row H ω y (i, x)) = LR.row H ω y (0, x) := by
    apply Finset.sum_eq_single 0
    · intro i _ hi
      exact LR.row_index H ω y (i, x) (by intro h; apply hi; exact Fin.ext h)
    · simp
  have hHighCap (ω : X.CΩ L.ht) (y : OddRole5 n) (x : Fin N) :
      (N : ℝ) * ∑ i : Fin (X.p.s n + 1), HR.row H ω y (i, x) ≤ 4 * Real.exp (X.p.DH n) := by
    have hsum : (∑ i : Fin (X.p.s n + 1), HR.row H ω y (i, x)) ≤
        (X.p.s n + 1 : ℕ) * (2 * Real.exp (X.p.DH n) / ((X.p.s n : ℝ) * N)) := by
      calc
        _ ≤ ∑ _i : Fin (X.p.s n + 1),
            2 * Real.exp (X.p.DH n) / ((X.p.s n : ℝ) * N) :=
          Finset.sum_le_sum fun i _ => HR.row_cap H ω y (i, x)
        _ = _ := by simp
    have hmul := mul_le_mul_of_nonneg_left hsum hNpos.le
    have hs1 : (1 : ℝ) ≤ X.p.s n := by exact_mod_cast Nat.succ_le_of_lt hsX
    have hh : (N : ℝ) * ((X.p.s n + 1 : ℕ) *
        (2 * Real.exp (X.p.DH n) / ((X.p.s n : ℝ) * N))) ≤ 4 * Real.exp (X.p.DH n) := by
      push_cast
      have hd : (N : ℝ) * ((X.p.s n + 1) *
          (2 * Real.exp (X.p.DH n) / ((X.p.s n : ℝ) * N))) =
          ((X.p.s n + 1) * (2 * Real.exp (X.p.DH n))) / X.p.s n := by
        field_simp [hspos.ne', hNpos.ne']
      rw [hd]
      apply (div_le_iff₀ hspos).mpr
      nlinarith [Real.exp_pos (X.p.DH n)]
    exact hmul.trans hh
  have hZnonneg : ∀ y ω x, 0 ≤ Z y ω x := by
    intro y ω x
    exact mul_nonneg hNpos.le (Finset.sum_nonneg fun i _ => X.oddRow_nonneg LR HR H ω y (i, x))
  have hZcap : ∀ y ω x, Z y ω x ≤ cap := by
    intro y ω x
    dsimp [Z, cap]
    simp only [oddRow, Finset.sum_add_distrib, mul_add, hLow]
    exact add_le_add (LR.row_cap H ω y (0, x)) (hHighCap ω y x)
  have hZlocal : ∀ y x, FinProb.DependsOn (fun ω => Z y ω x) (scope y) := by
    intro y x ω ω' hω
    have hl := LR.row_local H y ω ω' hω
    have hh := HR.row_local H y ω ω' hω
    simp [Z, oddRow, hl, hh]
  have hMean : ∀ x : Fin N,
      (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ y, μ.expect (fun ω => Z y ω x) ≤ B := by
    intro x
    have hlowMean (y : OddRole5 n) :
        μ.expect (fun ω => (N : ℝ) * LR.row H ω y (0, x)) ≤ LR.proxy H y x + 1 := by
      by_cases hl : X.g.low (X.p.J n) y.1
      · exact LR.long_vs_proxy H hH.good y x hl
      · simp only [LR.row_high H _ y (0, x) hl, mul_zero]
        rw [FinProb.expect_const]
        linarith [LR.proxy_nonneg H y x]
    have hhighMean (y : OddRole5 n) :
        μ.expect (fun ω => (N : ℝ) * ∑ i : Fin (X.p.s n + 1), HR.row H ω y (i, x)) ≤
          if ¬ X.g.low (X.p.J n) y.1 then 4 * Real.exp (X.p.DH n) else 0 := by
      apply le_trans (FinProb.expect_mono μ (fun ω => ?_)) (FinProb.expect_const μ _).le
      by_cases hl : X.g.low (X.p.J n) y.1
      · simp [hl, HR.row_low H ω y _ hl]
      · simpa [hl] using hHighCap ω y x
    have hpoint (y : OddRole5 n) : μ.expect (fun ω => Z y ω x) ≤
        LR.proxy H y x + 1 + (if ¬ X.g.low (X.p.J n) y.1 then 4 * Real.exp (X.p.DH n) else 0) := by
      have he : (fun ω => Z y ω x) =
          (fun ω => (N : ℝ) * LR.row H ω y (0, x) +
            (N : ℝ) * ∑ i : Fin (X.p.s n + 1), HR.row H ω y (i, x)) := by
        funext ω
        simp [Z, oddRow, Finset.sum_add_distrib, hLow, mul_add]
      rw [he, FinProb.expect_add]
      exact add_le_add (hlowMean y) (hhighMean y)
    have hhighAvg : (Fintype.card (OddRole5 n) : ℝ)⁻¹ *
        ∑ y : OddRole5 n, (if ¬ X.g.low (X.p.J n) y.1 then 4 * Real.exp (X.p.DH n) else 0) ≤ 1 :=
      Lane_sol_s05_centres.high_role_mean_bound X.p hnpos X.g hGeom
        (by simpa [hXp] using hJm) (by simpa [hXp] using hHighTail)
    have hcardNe : (Fintype.card (OddRole5 n) : ℝ) ≠ 0 := by
      rw [Lane_sol_s05_centres.odd_card n hnpos]
      positivity
    calc
      _ ≤ (Fintype.card (OddRole5 n) : ℝ)⁻¹ *
          ∑ y : OddRole5 n, (LR.proxy H y x + 1 +
            (if ¬ X.g.low (X.p.J n) y.1 then 4 * Real.exp (X.p.DH n) else 0)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hpoint y) (by positivity)
      _ = (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ y, LR.proxy H y x + 1 +
          (Fintype.card (OddRole5 n) : ℝ)⁻¹ *
            ∑ y : OddRole5 n, (if ¬ X.g.low (X.p.J n) y.1 then 4 * Real.exp (X.p.DH n) else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add, mul_add]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
          inv_mul_cancel₀ hcardNe]
      _ ≤ C + 1 + 1 := by linarith [hH.load_proxy x]
      _ = B := by dsimp [B]; ring
  have hNearCard : ∀ y, ((near y).card : ℝ) ≤ f * Fintype.card (OddRole5 n) := by
    intro y
    have hsmall := L.slack_small
    have hfixed := L.ht.fixed
    have hz : L.ht.ζ - L.ht.σ = 9 * p.alpha / 1000000 := by
      rw [hfixed.2.2.2.1, hfixed.2.2.1, hXp]
      ring
    rw [hz] at hsmall
    have hr : (L.ht.hp.r : ℝ) ≤ p.rho * n := by
      change (⌊X.p.rho * n⌋₊ : ℝ) ≤ _
      rw [hXp]
      exact Nat.floor_le (mul_nonneg p.hrho.1.le (Nat.cast_nonneg _))
    have hocc : ((Finset.univ \ X.g.residual).card : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Lane_sol_s05_centres.residual_complement]
      exact X.g.occupied_sublinear
    have hR : ((2 * (L.ht.hp.r + L.slack) + (Finset.univ \ X.g.residual).card : ℕ) : ℝ) ≤ q * n := by
      push_cast
      dsimp [q]
      have he : (9 * p.alpha / 1000000) / 4 = 9 * p.alpha / 4000000 := by ring
      rw [he] at hsmall
      linarith
    exact Lane_sol_s05_centres.odd_near_entropy X.g hnpos y.1 _ q hq0 hq hR
  have hFar : ∀ y y', y' ∉ near y → Disjoint (scope y) (scope y') := by
    intro y y' hfar
    have hd : 2 * (L.ht.hp.r + L.slack) < X.g.residualDist y'.1 y.1 := by
      have hn : ¬ X.g.residualDist y'.1 y.1 ≤ 2 * (L.ht.hp.r + L.slack) := by
        simpa [near] using hfar
      omega
    exact (Lane_sol_s05_centres.residual_scope_disjoint X.St y'.1 y.1
      (L.ht.hp.r + L.slack) hd).symm
  have hSelf : ∀ y, y ∈ near y := by
    intro y
    simp [near, ChunkGeometry5.residualDist]
  have hSmall : (n : ℝ) * f * cap ≤ B := by
    have hh : (n : ℝ) * f * cap ≤ 1 := by simpa [f, cap, hXp] using hNearCap
    exact hh.trans (by dsimp [B]; linarith)
  have hPerLabel : ∀ x : Fin N,
      μ.pr (fun ω => 8 * B < (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ y, Z y ω x) ≤ (1 / 4 : ℝ) ^ n := by
    intro x
    letI : Nonempty (OddRole5 n) := by
      apply Fintype.card_pos_iff.mp
      rw [Lane_sol_s05_centres.odd_card n hnpos]
      positivity
    exact Lane_sol_s05_centres.local_average_tail _ (fun y ω => Z y ω x) scope
      (fun y => hZlocal y x) (fun y ω => hZnonneg y ω x) cap (by dsimp [cap]; positivity)
      (fun y ω => hZcap y ω x) near hSelf hFar f hNearCard n B hB (hMean x) hSmall
  have hBad : ∀ ω : X.CΩ L.ht, L.success H ω ∧ ¬ X.OddLoadsOK LR HR H ω →
      ∃ x : Fin N, 8 * B < (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ y, Z y ω x := by
    intro ω hω
    by_contra hnone
    push_neg at hnone
    apply hω.2
    intro x
    let load : ℝ := ∑ y : OddRole5 n, ∑ i : Fin (X.p.s n + 1), X.oddRow LR HR H ω y (i, x)
    have hload : (∑ y : OddRole5 n, ∑ o : X.OddOut,
        if o.2 = x then X.oddRow LR HR H ω y o else 0) = load := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Fintype.sum_prod_type]
      simp
    rw [hload]
    have hz : (∑ y, Z y ω x) = (N : ℝ) * load := by
      dsimp [Z, load]
      rw [Finset.mul_sum]
    have hcardpos : (0 : ℝ) < Fintype.card (OddRole5 n) := by
      rw [Lane_sol_s05_centres.odd_card n hnpos]
      positivity
    have hAvg := hnone x
    rw [hz] at hAvg
    have hbound : (N : ℝ) * load ≤ 8 * B * Fintype.card (OddRole5 n) := by
      calc
        _ = (Fintype.card (OddRole5 n) : ℝ) *
            ((Fintype.card (OddRole5 n) : ℝ)⁻¹ * ((N : ℝ) * load)) := by field_simp
        _ ≤ (Fintype.card (OddRole5 n) : ℝ) * (8 * B) :=
          mul_le_mul_of_nonneg_left hAvg hcardpos.le
        _ = _ := by ring
    have hcard : (Fintype.card (OddRole5 n) : ℝ) ≤ (2 : ℝ) ^ n := by
      rw [Lane_sol_s05_centres.odd_card n hnpos]
      push_cast
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hsize : 8 * B * Fintype.card (OddRole5 n) ≤ (N : ℝ) * 1e-8 := by
      calc
        _ ≤ 8 * B * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_left hcard (by positivity)
        _ = 1e-8 * (C₀ * (2 : ℝ) ^ n) := by dsimp [C₀]; ring
        _ ≤ 1e-8 * N := mul_le_mul_of_nonneg_left hNlo (by norm_num)
        _ = _ := by ring
    nlinarith [hbound.trans hsize]
  have hUnion := FinProb.pr_exists_le_sum5 μ
    (fun x ω => 8 * B < (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ y, Z y ω x)
  calc
    _ ≤ μ.pr (fun ω => ∃ x : Fin N, 8 * B < (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ y, Z y ω x) :=
      FinProb.pr_mono μ _ _ hBad
    _ ≤ ∑ x : Fin N, μ.pr (fun ω => 8 * B < (Fintype.card (OddRole5 n) : ℝ)⁻¹ * ∑ y, Z y ω x) := hUnion
    _ ≤ ∑ _x : Fin N, (1 / 4 : ℝ) ^ n := Finset.sum_le_sum fun x _ => hPerLabel x
    _ = (N : ℝ) * (1 / 4 : ℝ) ^ n := by simp
    _ ≤ (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hNhi) (by positivity)
    _ = (n : ℝ) * (1 / 2 : ℝ) ^ n := by rw [mul_assoc, ← mul_pow]; norm_num
    _ ≤ 1 / 100 := hTailn.le

end Setup5

end

end HypercubeRamsey
