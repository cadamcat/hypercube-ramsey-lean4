import HypercubeRamsey.S05.History
import HypercubeRamsey.S05.Selection
import HypercubeRamsey.S03.Height.Selection
import HypercubeRamsey.S05.Centres_sol_s05_centres_scales
import HypercubeRamsey.S05.Centres_sol_s05_centres_records
import HypercubeRamsey.S05.Centres_sol_s05_centres_height
import HypercubeRamsey.S05.Centres_sol_s05_centres_low
import HypercubeRamsey.S05.Centres_sol_s05_centres_counts

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
            (X.centreLaw L.ht H).pr (fun ω => ¬ L.success H ω) ≤ 1 / 100 := by
  sorry

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
        -- The remaining comparison needs locality of the actual record and
        -- its observed arrays at this odd role's prescribed scope.
        sorry
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
          ∃ LR : X.LowRows5 L (cL p.pre1) (cH p.pre1), LR.proxyRadius ≤ Cloc := by
  sorry

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
