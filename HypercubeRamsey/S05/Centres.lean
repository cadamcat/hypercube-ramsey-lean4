import HypercubeRamsey.S05.History
import HypercubeRamsey.S05.Centres_q_s05_j34
import HypercubeRamsey.S05.Centres_opus_j4
import HypercubeRamsey.S05.Selection
import HypercubeRamsey.S03.Height.Selection
import HypercubeRamsey.S03.Clock.Leaves_p_clock_r2
import HypercubeRamsey.S05.Centres_sol_s05_g1
import HypercubeRamsey.S05.Centres_sol_s05_centres_scales
import HypercubeRamsey.S05.Centres_sol_s05_centres_records
import HypercubeRamsey.S05.Centres_sol_s05_centres_height
import HypercubeRamsey.S05.Centres_sol_s05_centres_low
import HypercubeRamsey.S05.Centres_sol_s05_centres_counts
import HypercubeRamsey.S05.Centres_sol_s05_k1
import HypercubeRamsey.S05.Centres_sol_s05_k1_rows
import HypercubeRamsey.S05.Centres_sol_s05_k1_records
import HypercubeRamsey.S05.Centres_sol_s05_k1_height
import HypercubeRamsey.S05.Centres_sol_s05_k1_mass
import HypercubeRamsey.S05.Centres_sol_s05_k1_lookup
import HypercubeRamsey.S05.Centres_sol_s05_k1_cap
import HypercubeRamsey.S05.Centres_sol_s05_k1_local
import HypercubeRamsey.S05.Centres_sol_s05_k1_keylocal
import HypercubeRamsey.S05.Centres_sol_s05_j5_stars
import HypercubeRamsey.S05.Centres_opus_j12
import HypercubeRamsey.S05.Centres_opus_j11

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
  classical
  intro ω ω' hagree
  have hpos (l : ht.hp.Loc) (hl : hammingDist l.1 s ≤ ht.hp.r + 16) :
      pos ω l = pos ω' l := by
    exact congrArg Prod.fst (hagree l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩))
  have harr (l : ht.hp.Loc) (hl : hammingDist l.1 s ≤ ht.hp.r + 16) (K : X.Ty) :
      arr ω l K = arr ω' l K := by
    exact congrArg (fun z => z.2.2.2 K)
      (hagree l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩))

  have evenNotSucc (m : ℕ) : Even m ↔ ¬ Even (m + 1) := by
    constructor
    · intro hm hsucc
      exact (Nat.not_even_iff_odd.mpr hm.add_one) hsucc
    · intro hsucc
      rcases Nat.even_or_odd m with hm | hm
      · exact hm
      · exact (hsucc hm.add_one).elim
  have evenSuccNot (m : ℕ) : Even (m + 1) ↔ ¬ Even m := Nat.even_add_one

  have hflip {u v : CubeVertex n} (huv : (cube n).Adj u v) :
      IsEvenRole u ↔ ¬ IsEvenRole v := by
    have hone : (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1 := huv
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
    have hdiff : u i ≠ v i := by
      have : i ∈ Finset.univ.filter (fun k : Fin n => u k ≠ v k) := by rw [hi]; simp
      exact (Finset.mem_filter.mp this).2
    have hsame : ∀ k, k ≠ i → u k = v k := by
      intro k hki
      by_contra hne
      have hk : k ∈ Finset.univ.filter (fun t : Fin n => u t ≠ v t) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      rw [hi] at hk
      exact hki (Finset.mem_singleton.mp hk)
    let A := Finset.univ.filter (fun k : Fin n => u k = true)
    let B := Finset.univ.filter (fun k : Fin n => v k = true)
    have hbit : (u i = false ∧ v i = true) ∨ (u i = true ∧ v i = false) := by
      cases hu : u i <;> cases hv : v i <;> simp_all
    rcases hbit with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · have hset : B = insert i A := by
        ext k
        by_cases hki : k = i
        · subst k
          simp [A, B, hu, hv]
        · have hk := hsame k hki
          simp [A, B, hki, hk]
      have hiA : i ∉ A := by simp [A, hu]
      change Even A.card ↔ ¬ Even B.card
      rw [hset, Finset.card_insert_of_notMem hiA]
      exact evenNotSucc A.card
    · have hset : A = insert i B := by
        ext k
        by_cases hki : k = i
        · subst k
          simp [A, B, hu, hv]
        · have hk := hsame k hki
          simp [A, B, hki, hk]
      have hiB : i ∉ B := by simp [B, hv]
      change Even A.card ↔ ¬ Even B.card
      rw [hset, Finset.card_insert_of_notMem hiB]
      exact evenSuccNot B.card

  have evenStateWitness (b : X.St.Site) (y : OddRole5 n) (hy : X.St.stateOf y.1 = b)
      (t : X.St.Site) (ht : t ∈ X.St.neighbors b) :
      ∃ x : CubeVertex n, X.St.stateOf x = t ∧ IsEvenRole x := by
    obtain ⟨x, z, hx, hz, hxz⟩ := (X.St.mem_neighbors b t).mp ht
    have hxOdd : ¬ IsEvenRole x := by
      intro hxEven
      have hdet := X.St.state_determines x y.1 (hx.trans hy.symm)
      exact y.2 (hdet.2.2.2.1.mp hxEven)
    have hzEven : IsEvenRole z := by
      by_contra hzOdd
      exact hxOdd ((hflip hxz).mpr hzOdd)
    exact ⟨z, hz, hzEven⟩

  have hProspSelf : prosp X ht (pos ω) s (j : ℕ) = prosp X ht (pos ω') s (j : ℕ) := by
    ext l
    simp only [prosp, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hp, hlev, hrad⟩
      exact ⟨(hpos l (by omega)).symm.trans hp, hlev, hrad⟩
    · rintro ⟨hp, hlev, hrad⟩
      exact ⟨(hpos l (by omega)).trans hp, hlev, hrad⟩

  have hStep3Arrays {Id : Type} [DecidableEq Id] (r : X.RecordOn Id)
      (A B : X.ArraysOn Id)
      (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
      (href : ∀ c ∈ r.2.2.1, (c.1, c.2.1) ∈ r.2.1)
      (hobs : ∀ c ∈ r.2.1, A c = B c) : X.step3FailOn H r A = X.step3FailOn H r B := by
    have hrefs := Lane_sol_s05_centres.refsOn_arrays_congr X H r A B href hobs
    have hgate (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
        X.candGateOn H r A θ = X.candGateOn H r B θ :=
      propext (Lane_sol_s05_hist1b.candGateOn_arrays_congr X H r A B hmask hobs θ)
    have hmass (e : Option (Id × X.Ty × Finset (Fin X.blockBound))) :
        X.step3MassOn H r A e = X.step3MassOn H r B e :=
      Lane_sol_s05_hist1b.step3MassOn_arrays_congr X H r A B hmask hobs e
    have hcap : X.HighCapped H r A = X.HighCapped H r B :=
      propext (Lane_sol_s05_centres.highCapped_arrays_congr X H r A B hmask hobs)
    have hprice : X.HighPriceFeasible H r A = X.HighPriceFeasible H r B :=
      propext (Lane_sol_s05_centres.highPrice_arrays_congr X H r A B hmask href hobs)
    simp only [Setup5.step3FailOn, hgate (H.2 r.1), hmass, hrefs, hcap, hprice]

  have hFailEq (b : X.St.Site) (hb : ∃ t ∈ X.St.neighbors b, X.St.oneHot t = s)
      (q : ℕ) : failSets X ht H (pos ω) (arraysOf ω) b q =
        failSets X ht H (pos ω') (arraysOf ω') b q := by
    rcases hb with ⟨t0, ht0, hts⟩
    have hdist8 (y : OddRole5 n) (hy : X.St.stateOf y.1 = b)
        (t : X.St.Site) (ht : t ∈ X.St.neighbors b) :
        hammingDist (X.St.oneHot t) s ≤ 8 := by
      rw [← hts]
      exact X.St.even_distance b t t0 ht ht0
        (evenStateWitness b y hy t ht) (evenStateWitness b y hy t0 ht0)
    have hProspAt' (y : OddRole5 n) (hy : X.St.stateOf y.1 = b)
        (t : X.St.Site) (htmem : t ∈ X.St.neighbors b) (k : ℕ) :
        prosp X ht (pos ω) (X.St.oneHot t) k = prosp X ht (pos ω') (X.St.oneHot t) k := by
      have hd := hdist8 y hy t htmem
      ext l
      simp only [prosp, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hp, hlev, hrad⟩
        have hl : hammingDist l.1 s ≤ ht.hp.r + 16 := by
          calc
            hammingDist l.1 s ≤ hammingDist l.1 (X.St.oneHot t) + hammingDist (X.St.oneHot t) s :=
              _root_.hammingDist_triangle l.1 (X.St.oneHot t) s
            _ ≤ ht.hp.r + 16 := by omega
        exact ⟨(hpos l hl).symm.trans hp, hlev, hrad⟩
      · rintro ⟨hp, hlev, hrad⟩
        have hl : hammingDist l.1 s ≤ ht.hp.r + 16 := by
          calc
            hammingDist l.1 s ≤ hammingDist l.1 (X.St.oneHot t) + hammingDist (X.St.oneHot t) s :=
              _root_.hammingDist_triangle l.1 (X.St.oneHot t) s
            _ ≤ ht.hp.r + 16 := by omega
        exact ⟨(hpos l hl).trans hp, hlev, hrad⟩
    have hlocalOf (μ : X.St.Site → ht.hp.Loc) (y : OddRole5 n)
        (hy : X.St.stateOf y.1 = b)
        (hm : ∀ t ∈ X.St.neighbors b,
          μ t ∈ prosp X ht (pos ω) (X.St.oneHot t) q ∪
            prosp X ht (pos ω) (X.St.oneHot t) (q + 1)) :
        ∀ t ∈ X.St.neighbors b, hammingDist (μ t).1 s ≤ ht.hp.r + 16 := by
      intro t htmem
      have hm' := hm t htmem
      have hd8 := hdist8 y hy t htmem
      rcases Finset.mem_union.mp hm' with hq | hq
      · have hd := (Finset.mem_filter.mp hq).2.2.2
        calc
          hammingDist (μ t).1 s ≤ hammingDist (μ t).1 (X.St.oneHot t) +
              hammingDist (X.St.oneHot t) s :=
            _root_.hammingDist_triangle (μ t).1 (X.St.oneHot t) s
          _ ≤ ht.hp.r + 16 := by omega
      · have hd := (Finset.mem_filter.mp hq).2.2.2
        calc
          hammingDist (μ t).1 s ≤ hammingDist (μ t).1 (X.St.oneHot t) +
              hammingDist (X.St.oneHot t) s :=
            _root_.hammingDist_triangle (μ t).1 (X.St.oneHot t) s
          _ ≤ ht.hp.r + 16 := by omega
    have hObs (y : OddRole5 n) (μ : X.St.Site → ht.hp.Loc) :
        (recordOf X ht H (arraysOf ω) (fun a => some (μ (X.St.stateOf a.1))) y).2.1 =
          (evenNbrs y).image (fun a => (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1)) := by
      ext c
      simp only [recordOf, Finset.mem_biUnion, Finset.mem_singleton, Finset.mem_image]
      constructor
      · rintro ⟨a, ha, hac⟩
        exact ⟨a, ha, hac.symm⟩
      · rintro ⟨a, ha, hac⟩
        exact ⟨a, ha, hac.symm⟩
    have hmaskObs (y : OddRole5 n) (μ : X.St.Site → ht.hp.Loc)
        (c : ht.hp.Loc × X.Ty) (M : Finset (Fin X.blockBound))
        (hc : (recordOf X ht H (arraysOf ω) (fun a => some (μ (X.St.stateOf a.1))) y).2.2.2 =
          some (c.1, c.2, M)) :
        c ∈ (recordOf X ht H (arraysOf ω) (fun a => some (μ (X.St.stateOf a.1))) y).2.1 := by
      classical
      dsimp only [recordOf] at hc
      cases hℓ : X.g.roleKey (X.p.J n) y.1 with
      | inl k =>
        by_cases hex : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none
        · have ha := Classical.choose_spec hex
          have heq : (μ (X.St.stateOf (Classical.choose hex).1),
              X.g.evenType (X.p.J n) (Classical.choose hex).1,
              X.firstK (X.hitSet (arraysOf ω)
                (μ (X.St.stateOf (Classical.choose hex).1),
                  X.g.evenType (X.p.J n) (Classical.choose hex).1)
                (X.lowCol H.2 k)) (X.p.usedBlocks n)) = (c.1, c.2, M) := by
            simpa [hℓ, hex] using hc
          rw [hObs]
          apply Finset.mem_image.mpr
          refine ⟨Classical.choose hex, ha.1, ?_⟩
          exact congrArg (fun z : ht.hp.Loc × X.Ty × Finset (Fin X.blockBound) => (z.1, z.2.1)) heq
        · simp [hℓ, hex] at hc
      | inr i => simp [hℓ] at hc
    have hRefSet (y : OddRole5 n) (μ : X.St.Site → ht.hp.Loc) :
        (recordOf X ht H (arraysOf ω) (fun a => some (μ (X.St.stateOf a.1))) y).2.2.1 =
          ((evenNbrs y).filter fun a =>
            X.g.roleKey (X.p.J n) y.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
              (X.g.roleKey (X.p.J n) y.1).isLeft =
                (X.g.evenType (X.p.J n) a.1).2.2.isSome).image
            (fun a => (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1,
              X.g.optionalKey (X.p.J n) a.1)) := by
      classical
      ext c
      constructor
      · intro hc
        change c ∈ (evenNbrs y).biUnion (fun a =>
          if X.g.roleKey (X.p.J n) y.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
              (X.g.roleKey (X.p.J n) y.1).isLeft =
                (X.g.evenType (X.p.J n) a.1).2.2.isSome then
            {(μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1,
              X.g.optionalKey (X.p.J n) a.1)} else ∅) at hc
        rcases Finset.mem_biUnion.mp hc with ⟨a, ha, hc⟩
        by_cases hp : X.g.roleKey (X.p.J n) y.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
            (X.g.roleKey (X.p.J n) y.1).isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome
        · simp [hp] at hc
          exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hp⟩, hc.symm⟩
        · simp [hp] at hc
      · intro hc
        obtain ⟨a, ha, hac⟩ := Finset.mem_image.mp hc
        have ha' := Finset.mem_filter.mp ha
        have hmem : c ∈ if X.g.roleKey (X.p.J n) y.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
            (X.g.roleKey (X.p.J n) y.1).isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome then
              {(μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1,
                X.g.optionalKey (X.p.J n) a.1)} else
              (∅ : Finset (ht.hp.Loc × X.Ty × Option X.Key)) := by
          simp [ha'.2, hac]
        exact Finset.mem_biUnion.mpr ⟨a, ha'.1, hmem⟩
    have hrefObs (y : OddRole5 n) (μ : X.St.Site → ht.hp.Loc)
        (c : ht.hp.Loc × X.Ty × Option X.Key)
        (hc : c ∈ (recordOf X ht H (arraysOf ω) (fun a => some (μ (X.St.stateOf a.1))) y).2.2.1) :
        (c.1, c.2.1) ∈
          (recordOf X ht H (arraysOf ω) (fun a => some (μ (X.St.stateOf a.1))) y).2.1 := by
      rw [hRefSet y μ] at hc
      obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hc
      rw [hObs]
      apply Finset.mem_image.mpr
      refine ⟨a, (Finset.mem_filter.mp ha).1, ?_⟩
      exact congrArg (fun z : ht.hp.Loc × X.Ty × Option X.Key => (z.1, z.2.1)) heq
    have hStep3Local (μ : X.St.Site → ht.hp.Loc) (y : OddRole5 n)
        (hy : X.St.stateOf y.1 = b)
        (hloc : ∀ t ∈ X.St.neighbors b, hammingDist (μ t).1 s ≤ ht.hp.r + 16) :
        X.step3FailOn H (recordOf X ht H (arraysOf ω) (fun a => some (μ (X.St.stateOf a.1))) y)
            (arraysOf ω) =
          X.step3FailOn H (recordOf X ht H (arraysOf ω') (fun a => some (μ (X.St.stateOf a.1))) y)
            (arraysOf ω') := by
      have hrecord :
          recordOf X ht H (arraysOf ω) (fun a => some (μ (X.St.stateOf a.1))) y =
            recordOf X ht H (arraysOf ω') (fun a => some (μ (X.St.stateOf a.1))) y := by
        classical
        cases hkey : X.g.roleKey (X.p.J n) y.1 with
        | inr i => simp [recordOf, hkey]
        | inl k =>
          by_cases hex : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none
          · have ha := Classical.choose_spec hex
            have htmem : X.St.stateOf (Classical.choose hex).1 ∈ X.St.neighbors b := by
              rw [X.St.mem_neighbors]
              exact ⟨y.1, (Classical.choose hex).1, hy, rfl,
                ((Finset.mem_filter.mp ha.1).2).symm⟩
            have hl := hloc _ htmem
            have hω := hagree (μ (X.St.stateOf (Classical.choose hex).1))
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
            have harray (K : X.Ty) :
                arraysOf ω (μ (X.St.stateOf (Classical.choose hex).1), K) =
                  arraysOf ω' (μ (X.St.stateOf (Classical.choose hex).1), K) := by
              change arr ω (μ (X.St.stateOf (Classical.choose hex).1)) K =
                arr ω' (μ (X.St.stateOf (Classical.choose hex).1)) K
              exact congrArg (fun z => z.2.2.2 K) hω
            have hhit :
                X.hitSet (arraysOf ω)
                    (μ (X.St.stateOf (Classical.choose hex).1),
                      X.g.evenType (X.p.J n) (Classical.choose hex).1)
                    (X.lowCol H.2 k) =
                  X.hitSet (arraysOf ω')
                    (μ (X.St.stateOf (Classical.choose hex).1),
                      X.g.evenType (X.p.J n) (Classical.choose hex).1)
                    (X.lowCol H.2 k) := by
              simp [Setup5.hitSet, harray]
            simp [recordOf, hkey, hex, hhit]
          · simp [recordOf, hkey, hex]
      let r := recordOf X ht H (arraysOf ω) (fun a => some (μ (X.St.stateOf a.1))) y
      have hobs : ∀ c ∈ r.2.1, arraysOf ω c = arraysOf ω' c := by
        intro c hc
        rw [hObs] at hc
        obtain ⟨a, ha, hca⟩ := Finset.mem_image.mp hc
        have ht : X.St.stateOf a.1 ∈ X.St.neighbors b := by
          rw [X.St.mem_neighbors]
          exact ⟨y.1, a.1, hy, rfl, (Finset.mem_filter.mp ha).2.symm⟩
        have hl := hloc (X.St.stateOf a.1) ht
        have hω := hagree (μ (X.St.stateOf a.1))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
        subst c
        change arr ω (μ (X.St.stateOf a.1)) (X.g.evenType (X.p.J n) a.1) =
          arr ω' (μ (X.St.stateOf a.1)) (X.g.evenType (X.p.J n) a.1)
        exact congrArg (fun z => z.2.2.2 (X.g.evenType (X.p.J n) a.1)) hω
      have hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1 := by
        intro c M hc
        exact hmaskObs y μ c M (by simpa [r] using hc)
      have href : ∀ c ∈ r.2.2.1, (c.1, c.2.1) ∈ r.2.1 := by
        intro c hc
        exact hrefObs y μ c (by simpa [r] using hc)
      have hstep := hStep3Arrays r (arraysOf ω) (arraysOf ω') hmask href hobs
      rw [← hrecord]
      exact hstep
    unfold failSets
    ext S
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨μ, hμ, hS⟩
      rcases hμ with ⟨hm, hcard, y, hy, hfail⟩
      have hloc := hlocalOf μ y hy hm
      refine ⟨μ, ⟨?_, hcard, y, hy, ?_⟩, hS⟩
      · intro t htmem
        have hq := Iff.of_eq (congrArg (fun F : Finset ht.hp.Loc => μ t ∈ F)
          (hProspAt' y hy t htmem q))
        have hq' := Iff.of_eq (congrArg (fun F : Finset ht.hp.Loc => μ t ∈ F)
          (hProspAt' y hy t htmem (q + 1)))
        exact Finset.mem_union.mpr ((or_congr hq hq').mp (Finset.mem_union.mp (hm t htmem)))
      · rw [hStep3Local μ y hy hloc] at hfail
        exact hfail
    · rintro ⟨μ, hμ, hS⟩
      rcases hμ with ⟨hm, hcard, y, hy, hfail⟩
      have hloc : ∀ t ∈ X.St.neighbors b, hammingDist (μ t).1 s ≤ ht.hp.r + 16 := by
        intro t htmem
        have hm' := hm t htmem
        have hd8 := hdist8 y hy t htmem
        rcases Finset.mem_union.mp hm' with hq | hq
        · have hd := (Finset.mem_filter.mp hq).2.2.2
          calc
            hammingDist (μ t).1 s ≤ hammingDist (μ t).1 (X.St.oneHot t) +
                hammingDist (X.St.oneHot t) s :=
              _root_.hammingDist_triangle (μ t).1 (X.St.oneHot t) s
            _ ≤ ht.hp.r + 16 := by omega
        · have hd := (Finset.mem_filter.mp hq).2.2.2
          calc
            hammingDist (μ t).1 s ≤ hammingDist (μ t).1 (X.St.oneHot t) +
                hammingDist (X.St.oneHot t) s :=
              _root_.hammingDist_triangle (μ t).1 (X.St.oneHot t) s
            _ ≤ ht.hp.r + 16 := by omega
      refine ⟨μ, ⟨?_, hcard, y, hy, ?_⟩, hS⟩
      · intro t htmem
        have hq := Iff.of_eq (congrArg (fun F : Finset ht.hp.Loc => μ t ∈ F)
          (hProspAt' y hy t htmem q))
        have hq' := Iff.of_eq (congrArg (fun F : Finset ht.hp.Loc => μ t ∈ F)
          (hProspAt' y hy t htmem (q + 1)))
        exact Finset.mem_union.mpr ((or_congr hq hq').mpr (Finset.mem_union.mp (hm t htmem)))
      · exact (hStep3Local μ y hy hloc).symm ▸ hfail

  have hMarks : marks X ht H (pos ω) (arraysOf ω) s (j : ℕ) =
      marks X ht H (pos ω') (arraysOf ω') s (j : ℕ) := by
    unfold marks
    ext l
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hl, hlev⟩
      rcases Finset.mem_biUnion.mp hl with ⟨b, hb, hrest⟩
      rcases Finset.mem_biUnion.mp hrest with ⟨q, hq, hinner⟩
      rcases Finset.mem_biUnion.mp hinner with ⟨S, hS, hls⟩
      have hb' := (Finset.mem_filter.mp hb).2
      have hS' : S ∈ Lane_sol_s05_centres.markingFamily
          (failSets X ht H (pos ω') (arraysOf ω') b q) := by
        rw [← hFailEq b hb' q]
        exact hS
      refine ⟨Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_biUnion.mpr ⟨q, hq,
        Finset.mem_biUnion.mpr ⟨S, hS', hls⟩⟩⟩, hlev⟩
    · rintro ⟨hl, hlev⟩
      rcases Finset.mem_biUnion.mp hl with ⟨b, hb, hrest⟩
      rcases Finset.mem_biUnion.mp hrest with ⟨q, hq, hinner⟩
      rcases Finset.mem_biUnion.mp hinner with ⟨S, hS, hls⟩
      have hb' := (Finset.mem_filter.mp hb).2
      have hS' : S ∈ Lane_sol_s05_centres.markingFamily
          (failSets X ht H (pos ω) (arraysOf ω) b q) := by
        rw [hFailEq b hb' q]
        exact hS
      refine ⟨Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_biUnion.mpr ⟨q, hq,
        Finset.mem_biUnion.mpr ⟨S, hS', hls⟩⟩⟩, hlev⟩

  have hsingle (l : ht.hp.Loc) (hl : hammingDist l.1 s ≤ ht.hp.r)
      (v : EvenRole5 n) :
      singletonOK X ht H (arraysOf ω) v l ↔ singletonOK X ht H (arraysOf ω') v l := by
    have hArr (K : X.Ty) : arraysOf ω (l, K) = arraysOf ω' (l, K) := by
      change arr ω l K = arr ω' l K
      exact harr l (by omega) K
    have hHit (K : X.Ty) (y : Fin N) :
        X.hitSet (arraysOf ω) (l, K) y = X.hitSet (arraysOf ω') (l, K) y := by
      simp [Setup5.hitSet, hArr]
    have hSub (K : X.Ty) (opt : Option X.Key) :
        X.refSubsetOn H (arraysOf ω) (l, K) opt =
          X.refSubsetOn H (arraysOf ω') (l, K) opt := by
      simp [Setup5.refSubsetOn, hHit]
    simp [singletonOK, heavyCountOn, hArr, hHit, hSub]

  have hTests (l : ht.hp.Loc) (hl : hammingDist l.1 s ≤ ht.hp.r) :
      (∀ v : EvenRole5 n, X.siteOf v = s → singletonOK X ht H (arraysOf ω) v l) ↔
        (∀ v : EvenRole5 n, X.siteOf v = s → singletonOK X ht H (arraysOf ω') v l) := by
    constructor
    · intro h v hv
      exact (hsingle l hl v).mp (h v hv)
    · intro h v hv
      exact (hsingle l hl v).mpr (h v hv)

  unfold markElig eligOf
  ext l
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hl, htests, hnot⟩
    have hlr := (Finset.mem_filter.mp hl).2.2.2
    refine ⟨?_, ?_⟩
    · rw [← hProspSelf]
      exact hl
    refine ⟨(hTests l hlr).mp htests, ?_⟩
    simpa [hMarks] using hnot
  · rintro ⟨hl, htests, hnot⟩
    have hlr := (Finset.mem_filter.mp hl).2.2.2
    refine ⟨?_, ?_⟩
    · rw [hProspSelf]
      exact hl
    refine ⟨(hTests l hlr).mpr htests, ?_⟩
    simpa [hMarks] using hnot

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
  have choose_congr : ∀ {α : Sort _} {p q : α → Prop} (hpq : p = q) (hp : ∃ x, p x) (hq : ∃ x, q x),
      Classical.choose hp = Classical.choose hq := by
    intro α p q hpq hp hq; subst hpq; rfl
  have recordOf_congr : ∀ (A : X.ArraysOn ht.hp.Loc) (σ₁ σ₂ : EvenRole5 n → Option ht.hp.Loc) (y : OddRole5 n),
      (∀ a ∈ evenNbrs y, σ₁ a = σ₂ a) → recordOf X ht H A σ₁ y = recordOf X ht H A σ₂ y := by
    intro A σ₁ σ₂ y h
    have hobs : (evenNbrs y).biUnion (fun a => match σ₁ a with
        | some l => {(l, X.g.evenType (X.p.J n) a.1)}
        | none => ∅) =
      (evenNbrs y).biUnion (fun a => match σ₂ a with
        | some l => {(l, X.g.evenType (X.p.J n) a.1)}
        | none => ∅) := by
      apply Finset.biUnion_congr rfl
      intro a ha
      rw [h a ha]
    have hrefs : (evenNbrs y).biUnion (fun a => match σ₁ a with
        | some l => if X.g.roleKey (X.p.J n) y.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
              (X.g.roleKey (X.p.J n) y.1).isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome then
            {(l, X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)} else ∅
        | none => ∅) =
      (evenNbrs y).biUnion (fun a => match σ₂ a with
        | some l => if X.g.roleKey (X.p.J n) y.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
              (X.g.roleKey (X.p.J n) y.1).isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome then
            {(l, X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)} else ∅
        | none => ∅) := by
      apply Finset.biUnion_congr rfl
      intro a ha
      rw [h a ha]
    have heq_p : (fun a => a ∈ evenNbrs y ∧ (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ₁ a).isSome) =
                 (fun a => a ∈ evenNbrs y ∧ (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ₂ a).isSome) := by
      funext a
      apply propext
      constructor
      · rintro ⟨ha, hnone, hsome⟩; rw [h a ha] at hsome; exact ⟨ha, hnone, hsome⟩
      · rintro ⟨ha, hnone, hsome⟩; rw [← h a ha] at hsome; exact ⟨ha, hnone, hsome⟩
    have hcond : (∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ₁ a).isSome) =
                 (∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ₂ a).isSome) :=
      congrArg Exists heq_p
    have hmask : (recordOf X ht H A σ₁ y).2.2.2 = (recordOf X ht H A σ₂ y).2.2.2 := by
      dsimp only [recordOf]
      rcases (X.g.roleKey (X.p.J n) y.1) with k | _
      · dsimp only
        by_cases h₁ : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ₁ a).isSome
        · have h₂ : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ₂ a).isSome := hcond ▸ h₁
          rw [dif_pos h₁, dif_pos h₂]
          have h_eq : Classical.choose h₁ = Classical.choose h₂ := choose_congr heq_p h₁ h₂
          have ha_mem : Classical.choose h₁ ∈ evenNbrs y := (Classical.choose_spec h₁).1
          have h_match : σ₁ (Classical.choose h₁) = σ₂ (Classical.choose h₂) := by
            rw [h_eq, h _ (h_eq ▸ ha_mem)]
          rw [h_match, h_eq]
        · have h₂ : ¬ (∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ₂ a).isSome) := fun h2 => h₁ (hcond.symm ▸ h2)
          rw [dif_neg h₁, dif_neg h₂]
      · rfl
    unfold recordOf
    dsimp only
    exact Prod.ext rfl (Prod.ext hobs (Prod.ext hrefs hmask))
  intro hfail
  have hrec_eq : X.actualRecordAt (markElig X ht H) H ω R y =
      recordOf X ht H (arraysOf ω) (fun a => some (μ (X.St.stateOf a.1))) y :=
    (actualRecordAt_eq X ht (markElig X ht H) H ω R y).trans (recordOf_congr (arraysOf ω) _ _ y hsel)
  have hfail' : X.step3FailOn H (recordOf X ht H (arraysOf ω) (fun a => some (μ (X.St.stateOf a.1))) y) (arraysOf ω) :=
    hrec_eq ▸ hfail
  let b := X.St.stateOf y.1
  let S := (X.St.neighbors b).image μ
  have hS : S ∈ failSets X ht H (pos ω) (arraysOf ω) b j := by
    simp only [failSets, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨μ, ⟨?_, hT, ⟨y, rfl, hfail'⟩⟩, rfl⟩
    intro t ht_nbr
    have h_elig := helig t ht_nbr
    simp only [markElig, eligOf, Finset.mem_filter] at h_elig
    have h_prosp := h_elig.1
    rcases hlev t ht_nbr with hj_eq | hj_eq
    · apply Finset.mem_union_left
      rw [hj_eq] at h_prosp
      exact h_prosp
    · apply Finset.mem_union_right
      rw [hj_eq] at h_prosp
      exact h_prosp
  have hn : 0 < n := by
    cases n with
    | zero =>
      have heven : IsEvenRole y.1 := by
        change Even (Finset.univ.filter (fun i : Fin 0 => y.1 i = true)).card
        rw [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty]
        exact ⟨0, rfl⟩
      exact (y.2 heven).elim
    | succ k => exact Nat.succ_pos k
  let i₀ : Fin n := ⟨0, hn⟩
  let v := cubeFlip y.1 i₀
  have hadj : (OAI.HypercubeRamsey.cube n).Adj y.1 v := cubeFlip_adj y.1 i₀
  have ht_mem : X.St.stateOf v ∈ X.St.neighbors b := by
    rw [X.St.mem_neighbors]
    exact ⟨y.1, v, rfl, rfl, hadj⟩
  have hS_non : S.Nonempty := ⟨μ (X.St.stateOf v), Finset.mem_image.mpr ⟨X.St.stateOf v, ht_mem, rfl⟩⟩
  have hspec := (Lane_sol_s05_centres.markingFamily_spec (failSets X ht H (pos ω) (arraysOf ω) b j)).2.2 S hS hS_non
  obtain ⟨l, hl_inter⟩ := hspec
  have hl_S := (Finset.mem_inter.mp hl_inter).1
  have hl_mf := (Finset.mem_inter.mp hl_inter).2
  obtain ⟨t, ht_nbr, rfl⟩ := Finset.mem_image.mp hl_S
  have h_elig := helig t ht_nbr
  simp only [markElig, eligOf, Finset.mem_filter] at h_elig
  have h_not_marks := h_elig.2.2
  have h_in_marks : μ t ∈ marks X ht H (pos ω) (arraysOf ω) (X.St.oneHot t) ((μ t).2 : ℕ) := by
    simp only [marks, Finset.mem_filter, and_true]
    apply Finset.mem_biUnion.mpr
    refine ⟨b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨t, ht_nbr, rfl⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨j, ?_, hl_mf⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le hj, ?_⟩
      rcases hlev t ht_nbr with h1 | h2
      · left; exact h1.symm
      · right; exact h2.symm
  exact h_not_marks h_in_marks

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
  classical
  intro p
  have hdimEv := Lane_sol_s05_centres.height_regime_eventually p
  obtain ⟨nDim, hDim⟩ := Filter.eventually_atTop.1 hdimEv
  let σ : ℝ := p.alpha / 1000000
  let ζ : ℝ := p.alpha / 100000
  have htopEv := Lane_sol_s05_centres.topScale_power_bound σ ζ
    (by dsimp [σ]; exact div_pos p.halpha.1 (by norm_num))
    (by dsimp [ζ]; have ha := p.halpha.2; nlinarith)
  obtain ⟨nTop, hTop⟩ := Filter.eventually_atTop.1 htopEv
  have hpolyEv : ∀ᶠ n : ℕ in Filter.atTop, 100000000000000 ≤ (n : ℝ) := by
    exact (tendsto_natCast_atTop_atTop.eventually_ge_atTop (100000000000000 : ℝ))
  obtain ⟨nPoly, hPoly⟩ := Filter.eventually_atTop.1 hpolyEv
  have hpowEv : ∀ᶠ n : ℕ in Filter.atTop, 48 ≤ (n : ℝ) ^ (9 : ℕ) :=
    hpolyEv.mono fun n hn => by
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by linarith
      have hpow : (2 : ℝ) ^ (9 : ℕ) ≤ (n : ℝ) ^ (9 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) hn2 9
      have hbase : (48 : ℝ) ≤ (2 : ℝ) ^ (9 : ℕ) := by norm_num
      exact hbase.trans hpow
  obtain ⟨nPow, hPow⟩ := Filter.eventually_atTop.1 hpowEv
  have hdecayEv : ∀ᶠ n : ℕ in Filter.atTop,
      30 * ((n : ℝ) * Real.exp (-(1 / 2 : ℝ) * (n : ℝ))) ≤ 1 := by
    have htend : Filter.Tendsto (fun n : ℕ => 30 * ((n : ℝ) * Real.exp (-(1 / 2 : ℝ) * (n : ℝ))))
        Filter.atTop (nhds 0) := by
      simpa only [Real.rpow_one, mul_zero, Function.comp_apply] using
        ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).comp
          tendsto_natCast_atTop_atTop).const_mul 30
    have hsmall := htend.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hsmall] with n hn
    change 30 * ((n : ℝ) * Real.exp (-(1 / 2 : ℝ) * (n : ℝ))) < 1 at hn
    exact hn.le
  obtain ⟨nDecay, hDecay⟩ := Filter.eventually_atTop.1 hdecayEv
  have hrhoEv : ∀ᶠ n : ℕ in Filter.atTop, 88 / p.rho ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (88 / p.rho)
  obtain ⟨nRho, hRho⟩ := Filter.eventually_atTop.1 hrhoEv
  let n₀ := max nDim (max nTop (max nPoly (max nPow (max nDecay nRho))))
  refine ⟨n₀, ?_⟩
  intro n hn N E G X hXp H
  subst p
  let ht := Lane_opus_s05.canonHt X
  let hp := ht.hp
  have hnDim : nDim ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnTop : nTop ≤ n :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hn)
  have hnPoly : nPoly ≤ n :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans hn))
  have hnPow : nPow ≤ n :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hn)))
  have hnDecay : nDecay ≤ n :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans
        ((Nat.le_max_right _ _).trans hn))))
  have hnRho : nRho ≤ n :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans
        ((Nat.le_max_right _ _).trans hn))))
  have hdim := hDim n hnDim (X.p.m n) (X.p.J n) X.g X.St
  have hdimLo : (n : ℝ) / 2 ≤ (hp.d : ℝ) := by
    calc
      (n : ℝ) / 2 = (1 / 2 : ℝ) * n := by ring
      _ ≤ hp.d := hdim.1
  have hdimHi : (hp.d : ℝ) ≤ 2 * n := hdim.2.1
  have hreg0 : (X.p.rho / 4) * (X.St.d : ℝ) ≤ ⌊X.p.rho * (n : ℝ)⌋₊ := by
    have h := hdim.2.2.1
    change (X.p.rho / 4) * (X.St.d : ℝ) ≤ ⌊X.p.rho * (n : ℝ)⌋₊ at h
    exact h
  have hreg : (X.p.rho / 4) * (hp.d : ℝ) ≤ hp.r := by
    simpa [hp, ht, Lane_opus_s05.canonHt, HeightChoice5.hp] using hreg0
  have hr : hp.r ≤ hp.d := by
    have h4Nat : 4 * hp.r ≤ hp.d := by
      have h := hdim.2.2.2
      change 4 * ⌊X.p.rho * (n : ℝ)⌋₊ ≤ X.St.d at h
      change 4 * hp.r ≤ hp.d
      simpa [hp, ht, Lane_opus_s05.canonHt, HeightChoice5.hp] using h
    omega
  have hr11 : 11 ≤ hp.r := by
    have hrhoPos : 0 < X.p.rho := X.p.hrho.1
    have hrlo : (X.p.rho / 8) * n ≤ hp.r := by
      have hmul := mul_le_mul_of_nonneg_left hdimLo
        (div_nonneg hrhoPos.le (by norm_num : (0 : ℝ) ≤ 4))
      have heq : (X.p.rho / 4) * ((n : ℝ) / 2) = (X.p.rho / 8) * n := by ring
      nlinarith [hreg]
    have hlarge : (11 : ℝ) ≤ (X.p.rho / 8) * n := by
      have hnR : 88 / X.p.rho ≤ (n : ℝ) := hRho n hnRho
      have hmul := (div_le_iff₀ hrhoPos).mp hnR
      nlinarith
    have hlargeR : (11 : ℝ) ≤ (hp.r : ℝ) := hlarge.trans hrlo
    exact_mod_cast hlargeR
  have hVlower : (n : ℝ) ^ 10 ≤ (hp.V : ℝ) := by
    have hchoose : (((hp.d + 1 - 11 : ℕ) : ℝ) ^ 11) / (Nat.factorial 11 : ℝ) ≤
        (Nat.choose hp.d 11 : ℝ) := by
      exact Nat.pow_le_choose 11 hp.d
    have hshift : (((hp.d + 1 - 11 : ℕ) : ℝ)) = (hp.d : ℝ) - 10 := by
      have h11d : 11 ≤ hp.d := Nat.le_trans hr11 hr
      have h11d' : 11 ≤ hp.d + 1 := h11d.trans (Nat.le_add_right hp.d 1)
      rw [Nat.cast_sub h11d']
      push_cast
      ring
    have hbase : (n : ℝ) / 3 ≤ ((hp.d + 1 - 11 : ℕ) : ℝ) := by
      rw [hshift]
      have hnR : 100000000000000 ≤ (n : ℝ) := by exact_mod_cast hPoly n hnPoly
      nlinarith [hdimLo]
    have hpower : ((n : ℝ) / 3) ^ 11 ≤ ((hp.d + 1 - 11 : ℕ) : ℝ) ^ 11 :=
      pow_le_pow_left₀ (by positivity) hbase 11
    have hfactorial : (0 : ℝ) < (Nat.factorial 11 : ℝ) := by norm_num
    have hchooseLower : ((n : ℝ) / 3) ^ 11 / (Nat.factorial 11 : ℝ) ≤
        (Nat.choose hp.d 11 : ℝ) :=
      (div_le_div_of_nonneg_right hpower hfactorial.le).trans hchoose
    have hconst : ((3 : ℝ) ^ 11) * (Nat.factorial 11 : ℝ) ≤ (n : ℝ) := by
      have hc : (3 : ℕ) ^ 11 * Nat.factorial 11 ≤ 100000000000000 := by norm_num
      have hnR : 100000000000000 ≤ (n : ℝ) := by exact_mod_cast hPoly n hnPoly
      have hcR : ((3 : ℝ) ^ 11) * (Nat.factorial 11 : ℝ) ≤ 100000000000000 := by exact_mod_cast hc
      exact le_trans hcR hnR
    have hnum : (n : ℝ) ^ 10 ≤ ((n : ℝ) / 3) ^ 11 / (Nat.factorial 11 : ℝ) := by
      rw [le_div_iff₀ hfactorial]
      rw [div_pow]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ 11)]
      have hmul := mul_le_mul_of_nonneg_right hconst (pow_nonneg (Nat.cast_nonneg n) 10)
      have hnPow : (n : ℝ) * (n : ℝ) ^ 10 = (n : ℝ) ^ 11 := by ring
      nlinarith [hmul, hnPow]
    have hchooseHi : (Nat.choose hp.d 11 : ℝ) ≤ (hp.V : ℝ) := by
      have hnat : Nat.choose hp.d 11 ≤ hp.V := by
        dsimp [HDParams.V]
        have hmem : 11 ∈ Finset.range (hp.r + 1) :=
          Finset.mem_range.mpr (Nat.lt_succ_of_le hr11)
        exact Finset.single_le_sum (fun i hi => Nat.zero_le _) hmem
      exact_mod_cast hnat
    exact hnum.trans (hchooseLower.trans hchooseHi)
  have hlam : hp.lam = (n : ℝ) ^ 10 := by
    simp [hp, ht, Lane_opus_s05.canonHt, HeightChoice5.hp]
  have hnPositive : (0 : ℝ) < (n : ℝ) := by
    have h := hPoly n hnPoly
    linarith
  have hnAtLeast1 : (1 : ℝ) ≤ (n : ℝ) := by
    have h := hPoly n hnPoly
    linarith
  have hVposR : (0 : ℝ) < (hp.V : ℝ) := by
    exact lt_of_lt_of_le (pow_pos hnPositive 10) hVlower
  have hVpos : 0 < hp.V := by exact_mod_cast hVposR
  have hlamPos : 0 < hp.lam := by rw [hlam]; exact pow_pos hnPositive 10
  have hprob : hp.lam / (hp.V : ℝ) ≤ 1 := by
    rw [hlam]
    exact (div_le_one hVposR).2 hVlower
  have hcubeCard : Fintype.card (CubeVertex hp.d) = 2 ^ hp.d := by
    simp [CubeVertex, Fintype.card_fun]
  have hsites : (X.sites ht).card ≤ 2 ^ hp.d := by
    calc
      (X.sites ht).card ≤ Fintype.card (CubeVertex hp.d) := Finset.card_le_univ _
      _ = 2 ^ hp.d := hcubeCard
  have hsitesR : ((X.sites ht).card : ℝ) ≤ Real.exp (2 * (n : ℝ)) := by
    calc
      ((X.sites ht).card : ℝ) ≤ (2 : ℝ) ^ hp.d := by exact_mod_cast hsites
      _ ≤ Real.exp (hp.d : ℝ) := by
        have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        calc
          (2 : ℝ) ^ hp.d ≤ (Real.exp 1) ^ hp.d := pow_le_pow_left₀ (by norm_num) htwo _
          _ = Real.exp (hp.d : ℝ) := by rw [← Real.exp_nat_mul]; congr 1 <;> ring
      _ ≤ Real.exp (2 * (n : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  have hH : ((hp.H + 1 : ℕ) : ℝ) ≤ 5 * n := by
    have htop := hTop n hnTop
    have htop' : (hp.H : ℝ) ≤ 4 * (n : ℝ) ^ (1 + σ - ζ) := by
      simpa [hp, ht, HeightChoice5.hp, Lane_opus_s05.canonHt, σ, ζ] using htop
    have hnR : 1 ≤ (n : ℝ) := hnAtLeast1
    have hexp : 1 + σ - ζ ≤ 1 := by dsimp [σ, ζ]; linarith [X.p.halpha.1]
    have hpow : (n : ℝ) ^ (1 + σ - ζ) ≤ (n : ℝ) := by
      calc
        _ ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnR hexp
        _ = n := by rw [Real.rpow_one]
    push_cast
    nlinarith [htop', hpow]
  have hnR : 1 ≤ (n : ℝ) := hnAtLeast1
  have hsqrt : Real.sqrt (n : ℝ) ≤ n := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hstrong : 2 * (n : ℝ) + Real.sqrt (n : ℝ) - (n : ℝ) ^ 10 / 12 ≤ -(n : ℝ) := by
    have hpow := hPow n hnPow
    have hmult : 48 * (n : ℝ) ≤ (n : ℝ) ^ 10 := by
      calc
        48 * (n : ℝ) ≤ (n : ℝ) ^ 9 * n := mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg n)
        _ = (n : ℝ) ^ 10 := by ring_nf
    nlinarith [hsqrt, hmult]
  have htail := height_position_counts hp (X.sites ht) hlamPos hVpos hr hprob
  have hham (u v : CubeVertex hp.d) : HypercubeRamsey.hammingDist u v = _root_.hammingDist u v := by
    simp [HypercubeRamsey.hammingDist, _root_.hammingDist]
  let rootCount (P : hp.Loc → Bool) (s : CubeVertex hp.d) (j : Fin (hp.H + 1)) : ℕ :=
    (Finset.univ.filter fun u : CubeVertex hp.d =>
      P (u, j) = true ∧ _root_.hammingDist u s ≤ hp.r).card
  let localCount (ω : X.CΩ ht) (s : CubeVertex hp.d) (j : Fin (hp.H + 1)) : ℕ :=
    (Finset.univ.filter fun u : CubeVertex hp.d =>
      pos ω (u, j) = true ∧ HypercubeRamsey.hammingDist u s ≤ hp.r).card
  let BadCounts (P : hp.Loc → Bool) : Prop :=
    ∃ s ∈ X.sites ht, ∃ j : Fin (hp.H + 1),
      ((rootCount P s j : ℝ) < hp.lam / 2 ∨ 2 * hp.lam < (rootCount P s j : ℝ))
  have countEq (ω : X.CΩ ht) (s : CubeVertex hp.d) (j : Fin (hp.H + 1)) :
      (rootCount (pos ω) s j : ℝ) = (localCount ω s j : ℝ) := by
    change ((Finset.univ.filter fun u : CubeVertex hp.d =>
        pos ω (u, j) = true ∧ _root_.hammingDist u s ≤ hp.r).card : ℝ) =
      ((Finset.univ.filter fun u : CubeVertex hp.d =>
        pos ω (u, j) = true ∧ HypercubeRamsey.hammingDist u s ≤ hp.r).card : ℝ)
    congr 1
  have hbad (ω : X.CΩ ht) : BadCounts (pos ω) ↔ ¬ BallsOK X ht ω := by
    classical
    constructor
    · rintro ⟨s, hs, j, hcount⟩ hgood
      have hpair := hgood s hs j
      have heq := countEq ω s j
      rcases hcount with hlo | hhi
      · have hlocal : (localCount ω s j : ℝ) < hp.lam / 2 := by
          rw [← heq]
          exact hlo
        exact (not_le_of_gt hlocal) hpair.1
      · have hlocal : 2 * hp.lam < (localCount ω s j : ℝ) := by
          rw [← heq]
          exact hhi
        exact (not_le_of_gt hlocal) hpair.2
    · intro hfail
      by_contra hnot
      apply hfail
      intro s hs j
      have heq := countEq ω s j
      constructor
      · by_contra hlo
        have hlocal : (localCount ω s j : ℝ) < hp.lam / 2 := not_le.mp hlo
        have hroot : (rootCount (pos ω) s j : ℝ) < hp.lam / 2 := by
          rw [heq]
          exact hlocal
        exact hnot ⟨s, hs, j, Or.inl hroot⟩
      · by_contra hhi
        have hlocal : 2 * hp.lam < (localCount ω s j : ℝ) := not_le.mp hhi
        have hroot : 2 * hp.lam < (rootCount (pos ω) s j : ℝ) := by
          rw [heq]
          exact hlocal
        exact hnot ⟨s, hs, j, Or.inr hroot⟩
  let pPresence : FinProb Bool := FinProb.bernoulli (hp.lam / (hp.V : ℝ))
  let pRest : FinProb (Bool × hp.TiePerm × (∀ K : X.Ty, X.Array K)) :=
    (FinProb.bernoulli ((n : ℝ) ^ ht.b₀ / hp.lam)).prod
      ((FinProb.uniformAll (Ω := hp.TiePerm) ⟨1⟩).prod
        (FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K))
  have hlocal : FinProb.map (FinProb.prod pPresence pRest) Prod.fst = pPresence := by
    apply FinProb.ext
    intro b
    change (∑ a : Bool × (Bool × hp.TiePerm × (∀ K : X.Ty, X.Array K)),
      if a.1 = b then pPresence.w a.1 * pRest.w a.2 else 0) = pPresence.w b
    rw [Fintype.sum_prod_type]
    simp only [Prod.fst, Prod.snd]
    calc
      (∑ x : Bool, ∑ y : Bool × hp.TiePerm × (∀ K : X.Ty, X.Array K),
          if x = b then pPresence.w x * pRest.w y else 0) =
          ∑ x : Bool, if x = b then pPresence.w x else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxb : x = b
        · simp [hxb, ← Finset.mul_sum, pRest.sum_eq_one]
        · simp [hxb]
      _ = pPresence.w b := by simp
  have hposLaw : FinProb.map (X.centreLaw ht H) (pos (X := X) (h := ht)) = hp.posLaw := by
    change FinProb.map (FinProb.pi (fun ℓ : hp.Loc =>
      (FinProb.bernoulli (hp.lam / (hp.V : ℝ))).prod
        ((FinProb.bernoulli ((n : ℝ) ^ ht.b₀ / hp.lam)).prod
          ((FinProb.uniformAll (Ω := hp.TiePerm) ⟨1⟩).prod
            (FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K)))))
      (fun ω ℓ => (ω ℓ).1) = hp.posLaw
    rw [FinProb.map_pi]
    apply FinProb.ext
    intro P
    change (∏ ℓ : hp.Loc,
        (FinProb.map
          ((FinProb.bernoulli (hp.lam / (hp.V : ℝ))).prod
            ((FinProb.bernoulli ((n : ℝ) ^ ht.b₀ / hp.lam)).prod
              ((FinProb.uniformAll (Ω := hp.TiePerm) ⟨1⟩).prod
                (FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K))))
          Prod.fst).w (P ℓ)) =
      ∏ ℓ : hp.Loc, (FinProb.bernoulli (hp.lam / (hp.V : ℝ))).w (P ℓ)
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    exact congrArg (fun Q : FinProb Bool => Q.w (P ℓ)) hlocal
  have hprobEq : (X.centreLaw ht H).pr (fun ω => ¬ BallsOK X ht ω) = hp.posLaw.pr (BadCounts) := by
    calc
      _ = (X.centreLaw ht H).pr (fun ω => BadCounts (pos ω)) := by
        apply congrArg
        funext ω
        exact propext (hbad ω).symm
      _ = (FinProb.map (X.centreLaw ht H) (pos (X := X) (h := ht))).pr BadCounts :=
        (FinProb.map_pr _ _ _).symm
      _ = hp.posLaw.pr BadCounts := by rw [hposLaw]
  have htailBound : (X.centreLaw ht H).pr (fun ω => ¬ BallsOK X ht ω) ≤
      2 * ((X.sites ht).card : ℝ) * ((hp.H + 1 : ℕ) : ℝ) * Real.exp (-hp.lam / 12) := by
    rw [hprobEq]
    simpa [BadCounts] using htail
  have hExpBound : 2 * ((X.sites ht).card : ℝ) * ((hp.H + 1 : ℕ) : ℝ) *
      Real.exp (-hp.lam / 12) ≤ 1 / 3 * Real.exp (-Real.sqrt n) := by
    rw [hlam]
    have hnlarge : 30 * ((n : ℝ) * Real.exp (-(1 / 2 : ℝ) * (n : ℝ))) ≤ 1 :=
      hDecay n hnDecay
    have hfac := mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ 2 * Real.exp (2 * (n : ℝ)))
    have hsiteNonneg : 0 ≤ ((X.sites ht).card : ℝ) := Nat.cast_nonneg _
    have hrest : 0 ≤ ((hp.H + 1 : ℕ) : ℝ) * Real.exp (-(n : ℝ) ^ 10 / 12) := by positivity
    calc
      _ ≤ (2 * Real.exp (2 * (n : ℝ))) * (5 * (n : ℝ)) *
          Real.exp (-(n : ℝ) ^ 10 / 12) := by
        have hfirst := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsitesR (by norm_num : (0 : ℝ) ≤ 2)) hrest
        calc
          2 * ((X.sites ht).card : ℝ) * ((hp.H + 1 : ℕ) : ℝ) *
              Real.exp (-(n : ℝ) ^ 10 / 12) ≤
            (2 * Real.exp (2 * (n : ℝ))) * ((hp.H + 1 : ℕ) : ℝ) *
              Real.exp (-(n : ℝ) ^ 10 / 12) := by nlinarith [hfirst]
          _ ≤ _ := by
            exact mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg _)
      _ = 10 * (n : ℝ) *
          (Real.exp (2 * (n : ℝ)) * Real.exp (-(n : ℝ) ^ 10 / 12)) := by ring
      _ = 10 * (n : ℝ) * Real.exp (2 * (n : ℝ) - (n : ℝ) ^ 10 / 12) := by
        calc
          _ = 10 * (n : ℝ) * Real.exp (2 * (n : ℝ) + (-(n : ℝ) ^ 10 / 12)) := by
            rw [Real.exp_add]
          _ = _ := by congr 2 <;> ring
      _ ≤ 10 * (n : ℝ) * Real.exp (-(n : ℝ) - Real.sqrt n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [hstrong]
      _ ≤ 1 / 3 * Real.exp (-Real.sqrt n) := by
        have hfactor : 30 * ((n : ℝ) * Real.exp (-(n : ℝ))) ≤ 1 := by
          have hexp : Real.exp (-(n : ℝ)) ≤ Real.exp (-(1 / 2 : ℝ) * (n : ℝ)) :=
            Real.exp_le_exp.mpr (by nlinarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg _])
          calc
            30 * ((n : ℝ) * Real.exp (-(n : ℝ))) =
                (30 * (n : ℝ)) * Real.exp (-(n : ℝ)) := by ring
            _ ≤ (30 * (n : ℝ)) * Real.exp (-(1 / 2 : ℝ) * (n : ℝ)) :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
            _ = 30 * ((n : ℝ) * Real.exp (-(1 / 2 : ℝ) * (n : ℝ))) := by ring
            _ ≤ 1 := hnlarge
        have hexpEq : Real.exp (-(n : ℝ) - Real.sqrt n) =
            Real.exp (-Real.sqrt n) * Real.exp (-(n : ℝ)) := by
          calc
            _ = Real.exp (-Real.sqrt n + (-(n : ℝ))) := by congr 1 <;> ring
            _ = _ := Real.exp_add _ _
        have heq : 10 * (n : ℝ) * Real.exp (-(n : ℝ) - Real.sqrt n) =
            (1 / 3 : ℝ) * Real.exp (-Real.sqrt n) *
              (30 * ((n : ℝ) * Real.exp (-(n : ℝ)))) := by
          rw [hexpEq]
          ring
        rw [heq]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)
            (Real.exp_nonneg (-Real.sqrt n)))
  calc
    _ ≤ 1 / 3 * Real.exp (-Real.sqrt n) := htailBound.trans hExpBound
    _ = Real.exp (-Real.sqrt n) / 3 := by ring

/-! #### J4 helpers: singleton tests read the arrays of one location (05:820–824) -/

theorem j4_singletonOK_iff (ht : X.HeightChoice5) (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc)
    (v : EvenRole5 n) (l : ht.hp.Loc) :
    singletonOK X ht H A v l ↔ Lane_opus_s05_j4.singleCond X H A l (X.g.evenType (X.p.J n) v.1)
      (X.g.optionalKey (X.p.J n) v.1) := Iff.rfl

theorem j4_singletonOK_local (ht : X.HeightChoice5) (H : X.KeyHist) (ω : X.CΩ ht)
    (v : EvenRole5 n) (l : ht.hp.Loc) :
    singletonOK X ht H (arraysOf ω) v l ↔
      singletonOK X ht H (fun c : ht.hp.Loc × X.Ty => (ω l).2.2.2 c.2) v l := Iff.rfl

/-- At a good history, an ID fails the singleton tests of the roles at a site with probability at
most `2 e^{-100}`: roles at one site share their state, hence their type and optional key. -/
theorem j4_site_fail_le (ht : X.HeightChoice5) (H : X.KeyHist) {cL cH : ℝ}
    (hgood : X.KeyGood5 H cL cH) (s : CubeVertex ht.hp.d) (l : ht.hp.Loc) (C : ℝ) (hC : 0 ≤ C)
    (hTail : ∀ K : X.Ty, (X.p.typeBlocks n K : ℝ) * Real.exp (-C * (X.p.typeSegs n K : ℝ)) ≤
      Real.exp (-100))
    (hKB : (X.p.q0 + (Real.log 2 + X.p.nu0 * |Real.log ((X.p.q0 : ℝ) * K')| + C) / X.p.Kpp) /
      X.p.nu0 ≤ X.p.KB)
    (hKh : X.p.a 1 + X.p.delta + 1 ≤ X.p.Kh) (hm : 1 < X.p.m n)
    (hused : 400 ≤ X.p.usedBlocks n) :
    (FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K).pr
      (fun arrs : (∀ K : X.Ty, X.Array K) =>
        ¬ ∀ v : EvenRole5 n, X.siteOf v = s →
          singletonOK X ht H (fun c : ht.hp.Loc × X.Ty => arrs c.2) v l) ≤
      2 * Real.exp (-100) := by
  classical
  by_cases hex : ∃ v₀ : EvenRole5 n, X.siteOf v₀ = s
  · obtain ⟨v₀, hv₀⟩ := hex
    have hbound := Lane_opus_s05_j4.single_fail_le X H hgood v₀.1 v₀.2 l C hC (hTail _) hKB hKh
      hm hused
    refine le_trans (FinProb.pr_mono _ _ _ ?_) hbound
    intro arrs hfail hok
    apply hfail
    intro v hv
    have hst : X.St.stateOf v.1 = X.St.stateOf v₀.1 :=
      X.St.oneHot_injective (show X.St.oneHot (X.St.stateOf v.1) =
        X.St.oneHot (X.St.stateOf v₀.1) from hv.trans hv₀.symm)
    have hdet := X.St.state_determines v.1 v₀.1 hst
    rw [j4_singletonOK_iff, hdet.2.2.2.2.1, hdet.2.2.2.2.2.1]
    exact hok
  · calc
      _ ≤ (FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) =>
            X.blockLaw H K).pr (fun _ => False) := by
        apply FinProb.pr_mono
        intro arrs hfail
        exact hfail fun v hv => absurd ⟨v, hv⟩ hex
      _ = 0 := by simp [FinProb.pr]
      _ ≤ 2 * Real.exp (-100) := by positivity

/-- The singleton losses at one site-level: independent indicators of mean `≤ 2 e^{-100} λ`
exceed `λ/12` with probability at most `exp(-λ/24)` (05:835–838). -/
theorem j4_count_tail (ht : X.HeightChoice5) (H : X.KeyHist) (s : CubeVertex ht.hp.d)
    (j : Fin (ht.hp.H + 1)) (hr : ht.hp.r ≤ ht.hp.d) (hlam : 0 ≤ ht.hp.lam)
    (hfail : ∀ l : ht.hp.Loc,
      (FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K).pr
        (fun arrs : (∀ K : X.Ty, X.Array K) =>
          ¬ ∀ v : EvenRole5 n, X.siteOf v = s →
            singletonOK X ht H (fun c : ht.hp.Loc × X.Ty => arrs c.2) v l) ≤ 2 * Real.exp (-100)) :
    (X.centreLaw ht H).pr (fun ω => ht.hp.lam / 12 <
      (((prosp X ht (pos ω) s (j : ℕ)).filter fun l =>
        ¬ ∀ v : EvenRole5 n, X.siteOf v = s → singletonOK X ht H (arraysOf ω) v l).card : ℝ)) ≤
      Real.exp (-ht.hp.lam / 24) := by
  classical
  let Q := FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K
  let Fs : ht.hp.Loc → (∀ K : X.Ty, X.Array K) → Prop := fun l arrs =>
    ¬ ∀ v : EvenRole5 n, X.siteOf v = s →
      singletonOK X ht H (fun c : ht.hp.Loc × X.Ty => arrs c.2) v l
  let inBall : ht.hp.Loc → Prop := fun l => l.2 = j ∧ hammingDist l.1 s ≤ ht.hp.r
  let Ev : ∀ _ : ht.hp.Loc, X.CVal ht → Prop := fun l c => c.1 = true ∧ (inBall l ∧ Fs l c.2.2.2)
  let perLoc : FinProb (X.CVal ht) := (FinProb.bernoulli (ht.hp.lam / (ht.hp.V : ℝ))).prod
      ((FinProb.bernoulli ((n : ℝ) ^ ht.b₀ / ht.hp.lam)).prod
        ((FinProb.uniformAll (Ω := ht.hp.TiePerm) ⟨1⟩).prod Q))
  have hlaw : X.centreLaw ht H = FinProb.pi fun _ : ht.hp.Loc => perLoc := rfl
  have hcount (ω : X.CΩ ht) : ((prosp X ht (pos ω) s (j : ℕ)).filter fun l =>
        ¬ ∀ v : EvenRole5 n, X.siteOf v = s → singletonOK X ht H (arraysOf ω) v l) =
      Finset.univ.filter fun l => Ev l (ω l) := by
    unfold prosp
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro l _
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, ⟨Fin.ext h2, h3⟩,
        fun hall => h4 fun v hv => (j4_singletonOK_local X ht H ω v l).2 (hall v hv)⟩
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
      exact ⟨⟨h1, congrArg Fin.val h2, h3⟩,
        fun hall => h4 fun v hv => (j4_singletonOK_local X ht H ω v l).1 (hall v hv)⟩
  have hE : Real.exp (-100) ≤ 1 / 200 := by
    have h50 : (51 : ℝ) ≤ Real.exp 50 := by linarith [Real.add_one_le_exp (50 : ℝ)]
    have h100 : Real.exp 100 = Real.exp 50 * Real.exp 50 := by rw [← Real.exp_add]; norm_num
    have hge : (200 : ℝ) ≤ Real.exp 100 := by rw [h100]; nlinarith
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hge
  have hVpos : (0 : ℝ) < ht.hp.V := by
    have h1 : 1 ≤ ht.hp.V := by
      unfold HDParams.V
      calc 1 = Nat.choose ht.hp.d 0 := by simp
        _ ≤ ∑ i ∈ Finset.range (ht.hp.r + 1), Nat.choose ht.hp.d i :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _) (by simp)
    exact_mod_cast h1
  have hq : 0 ≤ ht.hp.lam / (ht.hp.V : ℝ) := div_nonneg hlam hVpos.le
  have hEv (l : ht.hp.Loc) : perLoc.pr (Ev l) ≤
      ht.hp.lam / (ht.hp.V : ℝ) * (if inBall l then 2 * Real.exp (-100) else 0) := by
    have h := Lane_opus_s05_j4.cval_pr_le (ht.hp.lam / (ht.hp.V : ℝ))
      ((n : ℝ) ^ ht.b₀ / ht.hp.lam) hq (FinProb.uniformAll (Ω := ht.hp.TiePerm) ⟨1⟩) Q
      (fun arrs => inBall l ∧ Fs l arrs)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hq)
    by_cases hb : inBall l
    · rw [if_pos hb]
      exact (FinProb.pr_mono _ _ _ fun arrs h => h.2).trans (hfail l)
    · rw [if_neg hb]
      calc Q.pr (fun arrs => inBall l ∧ Fs l arrs) ≤ Q.pr (fun _ => False) :=
            FinProb.pr_mono _ _ _ fun arrs h => hb h.1
        _ = 0 := by simp [FinProb.pr]
  have hball : (Finset.univ.filter inBall).card = ht.hp.V := by
    have h1 : (Finset.univ.filter inBall).card = ∑ u : CubeVertex ht.hp.d,
        (Finset.univ.filter fun j' : Fin (ht.hp.H + 1) =>
          j' = j ∧ hammingDist u s ≤ ht.hp.r).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.card_filter]
    rw [h1]
    have hinner (u : CubeVertex ht.hp.d) : (Finset.univ.filter fun j' : Fin (ht.hp.H + 1) =>
        j' = j ∧ hammingDist u s ≤ ht.hp.r).card = if hammingDist u s ≤ ht.hp.r then 1 else 0 := by
      by_cases hu : hammingDist u s ≤ ht.hp.r
      · rw [if_pos hu, Finset.card_eq_one]
        exact ⟨j, by ext x; simp [hu]⟩
      · simp [hu]
    rw [Finset.sum_congr rfl fun u _ => hinner u, ← Finset.card_filter]
    exact Lane_p_height_main.cube_ball_card_eq_choose_sum s hr
  have hμ : ∑ l, perLoc.pr (Ev l) ≤ ht.hp.lam * (2 * Real.exp (-100)) := by
    calc
      ∑ l, perLoc.pr (Ev l) ≤ ∑ l : ht.hp.Loc,
          ht.hp.lam / (ht.hp.V : ℝ) * (if inBall l then 2 * Real.exp (-100) else 0) :=
        Finset.sum_le_sum fun l _ => hEv l
      _ = ht.hp.lam / (ht.hp.V : ℝ) *
          (((Finset.univ.filter inBall).card : ℝ) * (2 * Real.exp (-100))) := by
        rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          nsmul_eq_mul]
      _ = ht.hp.lam * (2 * Real.exp (-100)) := by
        rw [hball]
        field_simp
  have htail := Lane_opus_s05_j4.count_tail_exp (fun _ : ht.hp.Loc => perLoc) Ev
    (ht.hp.lam * (2 * Real.exp (-100))) (ht.hp.lam / 12) hμ
  rw [hlaw]
  calc
    _ ≤ (FinProb.pi fun _ : ht.hp.Loc => perLoc).pr (fun ω => ht.hp.lam / 12 ≤
          ((Finset.univ.filter fun l => Ev l (ω l)).card : ℝ)) := by
      apply FinProb.pr_mono
      intro ω hω
      rw [← hcount ω]
      exact hω.le
    _ ≤ Real.exp (2 * (ht.hp.lam * (2 * Real.exp (-100))) - ht.hp.lam / 12) := by
      convert htail
    _ ≤ Real.exp (-ht.hp.lam / 24) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hE hlam]

/-- SUB-LEMMA J4 (05:820–824,835–838): singleton losses, from independent arrays at distinct IDs
and the per-ID `o(1)` failure probability at good histories. -/
theorem singles_tail : ∀ (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
          (X.centreLaw (canonHt X) H).pr (fun ω => BallsOK X (canonHt X) ω ∧
            ¬ SinglesOK X (canonHt X) H ω) ≤ Real.exp (-Real.sqrt n) / 3 := by
  classical
  intro cL cH hc
  let R : ParamReq5 := {
    Kcap := fun _ => 0
    Kpp := fun _ => 0
    Kh := fun x => x.1 1 + x.2.2.2.1 + 1
    K1 := fun _ => 0
    K2 := fun _ => 0
    KD := fun _ => 0
    Ks := fun _ => 0
    KB := fun x =>
      let pre15 : Pre15 := x.1.1.1.1
      let pre0 : Pre05 := pre15.1
      let ν : ℝ := pre0.2.2.2.2.1
      let q₀ : ℝ := pre0.2.2.2.2.2.2.2
      let Kpp : ℝ := pre15.2.2.1
      let Kh : ℝ := pre15.2.2.2.1
      let eta : ℝ := pre15.2.2.2.2
      let K₁ : ℝ := x.1.1.1.2
      let C : ℝ := Kh * q₀ + q₀ / eta + q₀ / K₁ + 10
      (q₀ + (Real.log 2 + ν * |Real.log (q₀ * K')| + C) / Kpp) / ν
    alpha := fun _ => 1 / 50
    alpha_pos := fun _ => by norm_num
  }
  refine ⟨R, ?_⟩
  intro p hR
  rcases hR with ⟨_, _, hKh, _, _, _, _, hKB, _⟩
  let C : ℝ := p.Kh * p.q0 + p.q0 / p.eta + p.q0 / p.K1 + 10
  have hKhGap : p.a 1 + p.delta + 1 ≤ p.Kh := by
    simpa [R, Params5.pre0] using hKh
  have hKBReq :
      (p.q0 + (Real.log 2 + p.nu0 * |Real.log ((p.q0 : ℝ) * K')| + C) / p.Kpp) / p.nu0 ≤ p.KB := by
    simpa [R, C, Params5.pre5, Params5.pre4, Params5.pre3, Params5.pre2,
      Params5.pre1, Params5.pre0] using hKB
  have hCnn : 0 ≤ C := by
    have h1 : 0 ≤ p.Kh * (p.q0 : ℝ) := mul_nonneg p.hKh.le (Nat.cast_nonneg _)
    have h2 : 0 ≤ (p.q0 : ℝ) / p.eta := div_nonneg (Nat.cast_nonneg _) p.heta.1.le
    have h3 : 0 ≤ (p.q0 : ℝ) / p.K1 := div_nonneg (Nat.cast_nonneg _) p.hK1.le
    dsimp [C]
    linarith
  have hTailEv := Lane_opus_s05_j4.typeBlocks_tail_eventually p C le_rfl
  have hscEv := Lane_opus_s05_j4.scales_eventually p
  have hdimEv := Lane_sol_s05_centres.height_regime_eventually p
  let σ : ℝ := p.alpha / 1000000
  let ζ : ℝ := p.alpha / 100000
  have htopEv := Lane_sol_s05_centres.topScale_power_bound σ ζ
    (by dsimp [σ]; exact div_pos p.halpha.1 (by norm_num))
    (by dsimp [ζ]; have ha := p.halpha.2; nlinarith)
  have hfinEv := Lane_opus_s05_j4.final_tail_eventually
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (hTailEv.and (hscEv.and (hdimEv.and (htopEv.and (hfinEv.and (Filter.eventually_ge_atTop 1))))))
  refine ⟨n₀, ?_⟩
  intro n hn N E G X hXp H hgood
  obtain ⟨hTail, ⟨hm, hused⟩, hdimAll, htop, hfin, hn1⟩ := hn₀ n hn
  subst p
  let ht := Lane_opus_s05.canonHt X
  let hp := ht.hp
  have hdim := hdimAll (X.p.m n) (X.p.J n) X.g X.St
  have hr : hp.r ≤ hp.d := by
    have h4Nat : 4 * hp.r ≤ hp.d := by
      have h := hdim.2.2.2
      change 4 * ⌊X.p.rho * (n : ℝ)⌋₊ ≤ X.St.d at h
      change 4 * hp.r ≤ hp.d
      simpa [hp, ht, Lane_opus_s05.canonHt, HeightChoice5.hp] using h
    omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hdimHi : (hp.d : ℝ) ≤ 2 * n := hdim.2.1
  have hcubeCard : Fintype.card (CubeVertex hp.d) = 2 ^ hp.d := by
    simp [CubeVertex, Fintype.card_fun]
  have hsites : (X.sites ht).card ≤ 2 ^ hp.d := by
    calc
      (X.sites ht).card ≤ Fintype.card (CubeVertex hp.d) := Finset.card_le_univ _
      _ = 2 ^ hp.d := hcubeCard
  have hsitesR : ((X.sites ht).card : ℝ) ≤ Real.exp (2 * (n : ℝ)) := by
    calc
      ((X.sites ht).card : ℝ) ≤ (2 : ℝ) ^ hp.d := by exact_mod_cast hsites
      _ ≤ Real.exp (hp.d : ℝ) := by
        have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        calc
          (2 : ℝ) ^ hp.d ≤ (Real.exp 1) ^ hp.d := pow_le_pow_left₀ (by norm_num) htwo _
          _ = Real.exp (hp.d : ℝ) := by rw [← Real.exp_nat_mul]; congr 1 <;> ring
      _ ≤ Real.exp (2 * (n : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  have hH : ((hp.H + 1 : ℕ) : ℝ) ≤ 5 * n := by
    have htop' : (hp.H : ℝ) ≤ 4 * (n : ℝ) ^ (1 + σ - ζ) := by
      simpa [hp, ht, HeightChoice5.hp, Lane_opus_s05.canonHt, σ, ζ] using htop
    have hexp : 1 + σ - ζ ≤ 1 := by dsimp [σ, ζ]; linarith [X.p.halpha.1]
    have hpow : (n : ℝ) ^ (1 + σ - ζ) ≤ (n : ℝ) := by
      calc
        _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnR hexp
        _ = n := by rw [Real.rpow_one]
    push_cast
    nlinarith [htop', hpow]
  have hlam : hp.lam = (n : ℝ) ^ 10 := by
    simp [hp, ht, Lane_opus_s05.canonHt, HeightChoice5.hp]
  have hlam0 : 0 ≤ hp.lam := by rw [hlam]; positivity
  have hfail := fun (s : CubeVertex hp.d) (l : hp.Loc) =>
    j4_site_fail_le X ht H hgood s l C hCnn hTail hKBReq hKhGap hm hused
  have hcnt := fun (s : CubeVertex hp.d) (j : Fin (hp.H + 1)) =>
    j4_count_tail X ht H s j hr hlam0 (hfail s)
  calc
    (X.centreLaw (canonHt X) H).pr (fun ω => BallsOK X (canonHt X) ω ∧
        ¬ SinglesOK X (canonHt X) H ω) ≤
      (X.centreLaw ht H).pr (fun ω => ∃ sj : (X.sites ht) × Fin (hp.H + 1),
        hp.lam / 12 < (((prosp X ht (pos ω) sj.1.1 (sj.2 : ℕ)).filter fun l =>
          ¬ ∀ v : EvenRole5 n, X.siteOf v = sj.1.1 → singletonOK X ht H (arraysOf ω) v l).card : ℝ)) := by
      apply FinProb.pr_mono
      rintro ω ⟨_, hns⟩
      by_contra hcon
      apply hns
      intro s hs j
      by_contra hj
      have hj' := lt_of_not_ge hj
      have hjlt : j < hp.H + 1 := by
        by_contra hge
        have hge' : hp.H + 1 ≤ j := Nat.le_of_not_lt hge
        have hempty : ((prosp X ht (pos ω) s j).filter fun l =>
            ¬ ∀ v : EvenRole5 n, X.siteOf v = s → singletonOK X ht H (arraysOf ω) v l) = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro l hl
          have h2 : ((l.2 : Fin (hp.H + 1)) : ℕ) = j :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2.2.1
          have h3 : ((l.2 : Fin (hp.H + 1)) : ℕ) < hp.H + 1 := l.2.isLt
          omega
        rw [hempty, Finset.card_empty, Nat.cast_zero] at hj'
        linarith
      exact hcon ⟨(⟨s, hs⟩, ⟨j, hjlt⟩), hj'⟩
    _ ≤ ∑ sj : (X.sites ht) × Fin (hp.H + 1), (X.centreLaw ht H).pr (fun ω =>
        hp.lam / 12 < (((prosp X ht (pos ω) sj.1.1 (sj.2 : ℕ)).filter fun l =>
          ¬ ∀ v : EvenRole5 n, X.siteOf v = sj.1.1 → singletonOK X ht H (arraysOf ω) v l).card : ℝ)) :=
      FinProb.pr_exists_le_sum5 _ _
    _ ≤ ∑ _sj : (X.sites ht) × Fin (hp.H + 1), Real.exp (-hp.lam / 24) :=
      Finset.sum_le_sum fun sj _ => hcnt sj.1.1 sj.2
    _ = ((X.sites ht).card : ℝ) * ((hp.H + 1 : ℕ) : ℝ) * Real.exp (-hp.lam / 24) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ Real.exp (-Real.sqrt n) / 3 := by
      rw [hlam]
      exact hfin _ _ (Nat.cast_nonneg _) hsitesR (Nat.cast_nonneg _) hH

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
  intro p
  refine ⟨2, ?_⟩
  intro n hn N E G X hXp H ω hBalls hSingles hFamilies
  have hn2 : 2 ≤ n := hn
  let ht := canonHt X
  have hmPos : 0 < X.p.m n := by
    unfold Params5.m
    apply Nat.ceil_pos.mpr
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  have hmOne : 1 ≤ (X.p.m n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hmPos)
  have hmLe : X.p.m n ≤ n := by
    unfold Params5.m
    rw [Nat.ceil_le]
    have hnR : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 1 < n by omega)
    have hpow' : (n : ℝ) ^ X.p.alpha ≤ (n : ℝ) ^ (1 : ℝ) :=
      (Real.rpow_le_rpow_left_iff hnR).2 (by linarith [X.p.halpha.2])
    have hpow : (n : ℝ) ^ X.p.alpha ≤ n := by
      simpa only [Real.rpow_one] using hpow'
    exact hpow
  have hTle : (X.p.T n : ℝ) ≤ 2 * n := by
    have hT := Lane_sol_s05_h5l.T_upper X.p n hmOne
    have hpow : (X.p.m n : ℝ) ^ (1 / 1000 : ℝ) ≤ (X.p.m n : ℝ) :=
      Real.rpow_le_self_of_one_le hmOne (by norm_num)
    have hmLeR : (X.p.m n : ℝ) ≤ n := by exact_mod_cast hmLe
    calc
      (X.p.T n : ℝ) ≤ 2 * (X.p.m n : ℝ) ^ (1 / 1000 : ℝ) := hT
      _ ≤ 2 * (X.p.m n : ℝ) := by nlinarith
      _ ≤ 2 * n := by nlinarith
  have hn7 : 128 ≤ n ^ 7 := by
    calc
      128 = 2 ^ 7 := by norm_num
      _ ≤ n ^ 7 := by gcongr
  have hn7R : 96 ≤ (n : ℝ) ^ 7 := by
    have hcast : (128 : ℝ) ≤ (n : ℝ) ^ 7 := by exact_mod_cast hn7
    linarith
  have hpoly : 96 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 10 := by
    have hmul := mul_le_mul_of_nonneg_left hn7R (by positivity : 0 ≤ (n : ℝ) ^ 3)
    have hmul' : 96 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 * (n : ℝ) ^ 7 := by
      simpa [mul_comm] using hmul
    rw [← pow_add] at hmul'
    norm_num at hmul'
    exact hmul'
  change ht.hp.Legal (pos ω) (markElig X ht H ω) (X.sites ht)
  intro s hs j
  change (∀ l ∈ markElig X ht H ω s j,
      pos ω l = true ∧ l.2 = j ∧ hammingDist l.1 s ≤ ht.hp.r) ∧
    ht.hp.lam / 3 ≤ ((markElig X ht H ω s j).card : ℝ)
  constructor
  · intro l hl
    exact markElig_shape X ht H ω s j l hl
  · rcases Finset.mem_image.mp hs with ⟨a, ha, hsite⟩
    let Pset : Finset ht.hp.Loc := prosp X ht (pos ω) s j
    let Vset : Finset (CubeVertex ht.hp.d) := Finset.univ.filter fun u =>
      pos ω (u, j) = true ∧ hammingDist u s ≤ ht.hp.r
    let badSet : Finset ht.hp.Loc := Pset.filter fun l =>
      ¬ ∀ v : EvenRole5 n, X.siteOf v = s → singletonOK X ht H (arraysOf ω) v l
    let Mset : Finset ht.hp.Loc := marks X ht H (pos ω) (arraysOf ω) s j
    have hPsetEq : Pset = Vset.image (fun u => (u, j)) := by
      ext l
      constructor
      · intro hl
        simp only [Pset, prosp, Finset.mem_filter, Finset.mem_univ, true_and] at hl
        rcases hl with ⟨hpos, hrest⟩
        rcases hrest with ⟨hlev, hdist⟩
        have heq : l = (l.1, j) := Prod.ext rfl (Fin.ext hlev)
        have hpos' : pos ω (l.1, j) = true := by
          rw [heq] at hpos
          exact hpos
        refine Finset.mem_image.mpr ⟨l.1, ?_, heq.symm⟩
        simp only [Vset, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hpos', hdist⟩
      · intro hl
        rcases Finset.mem_image.mp hl with ⟨u, hu, rfl⟩
        simp only [Vset, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        simp only [Pset, prosp, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hu.1, hu.2⟩
    have hPsetCard : Pset.card = Vset.card := by
      calc
        Pset.card = (Vset.image (fun u => (u, j))).card := congrArg Finset.card hPsetEq
        _ = Vset.card := Finset.card_image_of_injective Vset
          (fun u v huv => congrArg Prod.fst huv)
    have hPcard : ht.hp.lam / 2 ≤ (Pset.card : ℝ) := by
      rw [hPsetCard]
      simpa [Vset, BallsOK] using (hBalls s hs j).1
    have hBadCard : (badSet.card : ℝ) ≤ ht.hp.lam / 12 := by
      simpa [badSet, Pset, prosp, SinglesOK] using (hSingles s hs (j : ℕ))
    let Bset : Finset X.St.Site := Finset.univ.filter fun b =>
      ∃ t ∈ X.St.neighbors b, X.St.oneHot t = s
    have hBsub : Bset ⊆ X.St.neighbors (X.St.stateOf a.1) := by
      intro b hb
      rcases (Finset.mem_filter.mp hb).2 with ⟨t, ht, hts⟩
      have hsite' : s = X.St.oneHot (X.St.stateOf a.1) := by
        simpa [ht, canonHt, HeightChoice5.hp, siteOf] using hsite.symm
      have hstate : t = X.St.stateOf a.1 := by
        apply X.St.oneHot_injective
        exact hts.trans hsite'
      apply (X.St.mem_neighbors (X.St.stateOf a.1) b).2
      rcases (X.St.mem_neighbors b t).1 ht with ⟨x, y, hx, hy, hxy⟩
      refine ⟨y, x, ?_, hx, hxy.symm⟩
      calc
        X.St.stateOf y = t := hy
        _ = X.St.stateOf a.1 := hstate
    have hBcard : Bset.card ≤ 2 * n := by
      calc
        Bset.card ≤ (X.St.neighbors (X.St.stateOf a.1)).card := Finset.card_le_card hBsub
        _ ≤ 2 * n := X.St.degree_bound _
    let levelSet : Finset ℕ := (Finset.range (ht.hp.H + 1)).filter fun k =>
      k = (j : ℕ) ∨ k + 1 = (j : ℕ)
    have hLevelSubset : levelSet ⊆ insert (j : ℕ) ({(j : ℕ) - 1} : Finset ℕ) := by
      intro k hk
      simp only [levelSet, Finset.mem_filter] at hk
      rcases hk.2 with hEq | hEq
      · simp [hEq]
      · have hpred : k = (j : ℕ) - 1 := by omega
        simp [hpred]
    have hLevelCard : levelSet.card ≤ 2 := by
      calc
        levelSet.card ≤ (insert (j : ℕ) ({(j : ℕ) - 1} : Finset ℕ)).card :=
          Finset.card_le_card hLevelSubset
        _ ≤ ({(j : ℕ) - 1} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
        _ ≤ 1 + 1 := by simp
        _ = 2 := by norm_num
    have hfamily (b : X.St.Site) (k : ℕ) :
        ((Lane_sol_s05_centres.markingFamily (failSets X ht H (pos ω) (arraysOf ω) b k)).biUnion id).card ≤
          n * X.p.T n := by
      let F := failSets X ht H (pos ω) (arraysOf ω) b k
      have hsmall : (Lane_sol_s05_centres.markingFamily F).card ≤ n :=
        Nat.le_of_lt (hFamilies b k)
      have hsize : ∀ S ∈ F, S.card ≤ X.p.T n := by
        intro S hS
        rcases Finset.mem_image.mp hS with ⟨μ, hμ, rfl⟩
        exact (Finset.mem_filter.mp hμ).2.2.1
      exact Lane_sol_s05_centres.marking_card_bound F n (X.p.T n) hsmall hsize
    let Uset : Finset ht.hp.Loc := Bset.biUnion fun b => levelSet.biUnion fun k =>
      (Lane_sol_s05_centres.markingFamily
        (failSets X ht H (pos ω) (arraysOf ω) b k)).biUnion id
    have hMsubset : Mset ⊆ Uset := by
      intro l hl
      simp only [Mset, marks, Finset.mem_filter] at hl
      rcases Finset.mem_biUnion.mp hl.1 with ⟨b, hb, hlb⟩
      rcases Finset.mem_biUnion.mp hlb with ⟨k, hk, hlk⟩
      unfold Uset
      refine Finset.mem_biUnion.mpr ⟨b, ?_, Finset.mem_biUnion.mpr ⟨k, ?_, hlk⟩⟩
      · simpa [Bset] using hb
      · simpa [levelSet] using hk
    have hUcard : Uset.card ≤ Bset.card * (levelSet.card * (n * X.p.T n)) := by
      unfold Uset
      calc
        _ ≤ ∑ b ∈ Bset, (levelSet.biUnion fun k =>
            (Lane_sol_s05_centres.markingFamily
              (failSets X ht H (pos ω) (arraysOf ω) b k)).biUnion id).card := Finset.card_biUnion_le
        _ ≤ ∑ b ∈ Bset, ∑ k ∈ levelSet, n * X.p.T n := by
          apply Finset.sum_le_sum
          intro b hb
          calc
            _ ≤ ∑ k ∈ levelSet,
              ((Lane_sol_s05_centres.markingFamily
                (failSets X ht H (pos ω) (arraysOf ω) b k)).biUnion id).card :=
                Finset.card_biUnion_le
            _ ≤ ∑ k ∈ levelSet, n * X.p.T n :=
              Finset.sum_le_sum fun k hk => hfamily b k
        _ = Bset.card * (levelSet.card * (n * X.p.T n)) := by simp [mul_assoc]
    have hMcard : Mset.card ≤ 4 * n ^ 2 * X.p.T n := by
      calc
        Mset.card ≤ Uset.card := Finset.card_le_card hMsubset
        _ ≤ Bset.card * (levelSet.card * (n * X.p.T n)) := hUcard
        _ ≤ (2 * n) * (2 * (n * X.p.T n)) :=
          Nat.mul_le_mul hBcard (Nat.mul_le_mul_right _ hLevelCard)
        _ = 4 * n ^ 2 * X.p.T n := by ring
    have hMcardR : (Mset.card : ℝ) ≤ ht.hp.lam / 12 := by
      have hcardR : (Mset.card : ℝ) ≤ 4 * (n : ℝ) ^ 2 * (X.p.T n : ℝ) := by
        exact_mod_cast hMcard
      have hsmall : (Mset.card : ℝ) ≤ (n : ℝ) ^ 10 / 12 := by
        calc
          (Mset.card : ℝ) ≤ 4 * (n : ℝ) ^ 2 * (X.p.T n : ℝ) := hcardR
          _ ≤ 8 * (n : ℝ) ^ 3 := by nlinarith [hTle]
          _ ≤ (n : ℝ) ^ 10 / 12 := by nlinarith [hpoly]
      simpa [ht, canonHt, HeightChoice5.hp] using hsmall
    have hEsub : markElig X ht H ω s j ⊆ Pset := by
      intro l hl
      have hl' := hl
      dsimp only [markElig, eligOf] at hl'
      exact (Finset.mem_filter.mp hl').1
    have hLostSub : Pset \ markElig X ht H ω s j ⊆ badSet ∪ Mset := by
      intro l hl
      rcases Finset.mem_sdiff.mp hl with ⟨hlP, hlnE⟩
      by_cases hgood : ∀ v : EvenRole5 n, X.siteOf v = s → singletonOK X ht H (arraysOf ω) v l
      · apply Finset.mem_union.mpr
        right
        have hM : l ∈ Mset := by
          by_contra hlnM
          have hlnE' := hlnE
          dsimp only [markElig, eligOf] at hlnE'
          simp only [Finset.mem_filter] at hlnE'
          have hnotM : l ∉ marks X ht H (pos ω) (arraysOf ω) s j := by
            simpa [Mset] using hlnM
          exact hlnE' ⟨hlP, ⟨hgood, hnotM⟩⟩
        exact hM
      · apply Finset.mem_union.mpr
        left
        exact Finset.mem_filter.mpr ⟨hlP, hgood⟩
    have hLostCard :
        (Pset \ markElig X ht H ω s j).card ≤ badSet.card + Mset.card := by
      calc
        (Pset \ markElig X ht H ω s j).card ≤ (badSet ∪ Mset).card :=
          Finset.card_le_card hLostSub
        _ ≤ badSet.card + Mset.card := Finset.card_union_le _ _
    have hCardEq : ((Pset \ markElig X ht H ω s j).card : ℝ) +
        ((markElig X ht H ω s j).card : ℝ) = (Pset.card : ℝ) := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hEsub
    have hLostCardR : ((Pset \ markElig X ht H ω s j).card : ℝ) ≤
        (badSet.card : ℝ) + (Mset.card : ℝ) := by exact_mod_cast hLostCard
    have hTotal : (Pset.card : ℝ) ≤ (markElig X ht H ω s j).card +
        (badSet.card : ℝ) + (Mset.card : ℝ) := by linarith
    change ht.hp.lam / 3 ≤ ((markElig X ht H ω s j).card : ℝ)
    linarith [hPcard, hBadCard, hMcardR, hTotal]

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

set_option maxHeartbeats 1000000
/-- SUB-LEMMA J10 (union bound over J3–J9): the two probability estimates of L5.1j. -/
theorem markElig_estimates : ∀ (C : ℝ) (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        X.RecordCount C → ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
          (X.centreLaw (canonHt X) H).pr (fun ω =>
              ¬ (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω) (X.sites (canonHt X))) ≤
            Real.exp (-Real.sqrt n) ∧
          (X.centreLaw (canonHt X) H).pr (fun ω => ¬ CentreSuccess X (canonHt X) H ω) ≤ 1 / 100 := by
  intro C cL cH hc
  obtain ⟨Rsing, hRsing⟩ := singles_tail cL cH hc
  obtain ⟨Rfam, hRfam⟩ := families_tail C cL cH hc
  obtain ⟨Rsup, hRsup⟩ := support_tail cL cH hc
  let R := (Rsing.join Rfam).join Rsup
  refine ⟨R, ?_⟩
  intro p hR
  obtain ⟨hRsf, hRsup'⟩ := ParamReq5.holds_of_join hR
  obtain ⟨hRsing', hRfam'⟩ := ParamReq5.holds_of_join hRsf
  obtain ⟨nBalls, hBallsN⟩ := balls_tail p
  obtain ⟨nSing, hSingN⟩ := hRsing p hRsing'
  obtain ⟨nFam, hFamN⟩ := hRfam p hRfam'
  obtain ⟨nSup, hSupN⟩ := hRsup p hRsup'
  obtain ⟨nLeg, hLegN⟩ := legal_of_events p
  obtain ⟨nHeight, hHeightN⟩ := heights_tail p
  obtain ⟨nSuccess, hSuccessN⟩ := success_of_events p
  have hexpLim := by
    simpa only [Function.comp_apply] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨nExp, hExpN⟩ := Filter.eventually_atTop.mp
    (hexpLim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 400)))
  let n01 := max nBalls nSing
  let n02 := max n01 nFam
  let n03 := max n02 nSup
  let n04 := max n03 nLeg
  let n05 := max n04 nHeight
  let n06 := max n05 nSuccess
  let n0 := max n06 nExp
  refine ⟨n0, ?_⟩
  intro n hn N E G X hXp hRC H hH
  have hn06 : n06 ≤ n := (le_max_left _ _).trans hn
  have hnExp : nExp ≤ n := (le_max_right _ _).trans hn
  have hnSuccess : nSuccess ≤ n := (le_max_right _ _).trans hn06
  have hn05 : n05 ≤ n := (le_max_left _ _).trans hn06
  have hn04 : n04 ≤ n := (le_max_left _ _).trans hn05
  have hnHeight : nHeight ≤ n := (le_max_right _ _).trans hn05
  have hn03 : n03 ≤ n := (le_max_left _ _).trans hn04
  have hnLeg : nLeg ≤ n := (le_max_right _ _).trans hn04
  have hn02 : n02 ≤ n := (le_max_left _ _).trans hn03
  have hnSup : nSup ≤ n := (le_max_right _ _).trans hn03
  have hn01 : n01 ≤ n := (le_max_left _ _).trans hn02
  have hnFam : nFam ≤ n := (le_max_right _ _).trans hn02
  have hnBalls : nBalls ≤ n := (le_max_left _ _).trans hn01
  have hnSing : nSing ≤ n := (le_max_right _ _).trans hn01
  let μ := X.centreLaw (canonHt X) H
  let badBalls : X.CΩ (canonHt X) → Prop := fun ω => ¬ BallsOK X (canonHt X) ω
  let badSingles : X.CΩ (canonHt X) → Prop := fun ω =>
    BallsOK X (canonHt X) ω ∧ ¬ SinglesOK X (canonHt X) H ω
  let badFamilies : X.CΩ (canonHt X) → Prop := fun ω =>
    BallsOK X (canonHt X) ω ∧ ¬ FamiliesOK X (canonHt X) H ω
  let badLegal : X.CΩ (canonHt X) → Prop := fun ω =>
    ¬ (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω) (X.sites (canonHt X))
  let badHeights : X.CΩ (canonHt X) → Prop := fun ω =>
    (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω) (X.sites (canonHt X)) ∧
      ¬ (canonHt X).hp.GoodHeights (X.sites (canonHt X)) (pos ω) (act ω)
        (markElig X (canonHt X) H ω)
  let badSupport : X.CΩ (canonHt X) → Prop := fun ω => ¬ SupportOK X (canonHt X) H ω
  let badSuccess : X.CΩ (canonHt X) → Prop := fun ω => ¬ CentreSuccess X (canonHt X) H ω
  have hBallsPr : μ.pr badBalls ≤ Real.exp (-Real.sqrt n) / 3 := by
    simpa [μ, badBalls] using hBallsN n hnBalls N E G X hXp H
  have hSinglesPr : μ.pr badSingles ≤ Real.exp (-Real.sqrt n) / 3 := by
    simpa [μ, badSingles] using hSingN n hnSing N E G X hXp H hH
  have hFamiliesPr : μ.pr badFamilies ≤ Real.exp (-Real.sqrt n) / 3 := by
    simpa [μ, badFamilies] using hFamN n hnFam N E G X hXp hRC H hH
  have hSupportPr : μ.pr badSupport ≤ 1 / 300 := by
    simpa [μ, badSupport] using hSupN n hnSup N E G X hXp H hH
  have hHeightsPr : μ.pr badHeights ≤ 1 / 300 := by
    simpa [μ, badHeights] using hHeightN n hnHeight N E G X hXp H
  have hLegDet : ∀ ω, BallsOK X (canonHt X) ω → SinglesOK X (canonHt X) H ω →
      FamiliesOK X (canonHt X) H ω →
        (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω) (X.sites (canonHt X)) := by
    intro ω hB hS hF
    exact hLegN n hnLeg N E G X hXp H ω hB hS hF
  have hLegalCover : ∀ ω, badLegal ω →
      badBalls ω ∨ badSingles ω ∨ badFamilies ω := by
    intro ω hnotLegal
    by_cases hB : BallsOK X (canonHt X) ω
    · by_cases hS : SinglesOK X (canonHt X) H ω
      · by_cases hF : FamiliesOK X (canonHt X) H ω
        · exact (hnotLegal (hLegDet ω hB hS hF)).elim
        · exact Or.inr (Or.inr ⟨hB, hF⟩)
      · exact Or.inr (Or.inl ⟨hB, hS⟩)
    · exact Or.inl hB
  have hLegalUnion :
      μ.pr (fun ω => badBalls ω ∨ badSingles ω ∨ badFamilies ω) ≤
        μ.pr badBalls + μ.pr badSingles + μ.pr badFamilies := by
    calc
      _ ≤ μ.pr badBalls + μ.pr (fun ω => badSingles ω ∨ badFamilies ω) :=
        FinProb.pr_union μ badBalls (fun ω => badSingles ω ∨ badFamilies ω)
      _ ≤ μ.pr badBalls + (μ.pr badSingles + μ.pr badFamilies) := by
        have hu := FinProb.pr_union μ badSingles badFamilies
        nlinarith [hu]
      _ = μ.pr badBalls + μ.pr badSingles + μ.pr badFamilies := by ring
  have hLegalPr : μ.pr badLegal ≤ Real.exp (-Real.sqrt n) := by
    calc
      μ.pr badLegal ≤ μ.pr (fun ω => badBalls ω ∨ badSingles ω ∨ badFamilies ω) :=
        FinProb.pr_mono μ _ _ hLegalCover
      _ ≤ μ.pr badBalls + μ.pr badSingles + μ.pr badFamilies := hLegalUnion
      _ ≤ Real.exp (-Real.sqrt n) / 3 + Real.exp (-Real.sqrt n) / 3 +
          Real.exp (-Real.sqrt n) / 3 := by linarith [hBallsPr, hSinglesPr, hFamiliesPr]
      _ = Real.exp (-Real.sqrt n) := by ring
  have hSuccessDet : ∀ ω,
      (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω) (X.sites (canonHt X)) →
      BallsOK X (canonHt X) ω →
      (canonHt X).hp.GoodHeights (X.sites (canonHt X)) (pos ω) (act ω)
        (markElig X (canonHt X) H ω) →
      SupportOK X (canonHt X) H ω → CentreSuccess X (canonHt X) H ω := by
    intro ω hL hB hHt hSup'
    exact hSuccessN n hnSuccess N E G X hXp H ω hH.base_support hH.step1 hL hB hHt hSup'
  have hSuccessCover : ∀ ω, badSuccess ω →
      badLegal ω ∨ badBalls ω ∨ badHeights ω ∨ badSupport ω := by
    intro ω hnotSuccess
    by_cases hL : (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω)
        (X.sites (canonHt X))
    · by_cases hB : BallsOK X (canonHt X) ω
      · by_cases hHt : (canonHt X).hp.GoodHeights (X.sites (canonHt X)) (pos ω)
          (act ω) (markElig X (canonHt X) H ω)
        · by_cases hSup' : SupportOK X (canonHt X) H ω
          · exact (hnotSuccess (hSuccessDet ω hL hB hHt hSup')).elim
          · exact Or.inr (Or.inr (Or.inr hSup'))
        · exact Or.inr (Or.inr (Or.inl ⟨hL, hHt⟩))
      · exact Or.inr (Or.inl hB)
    · exact Or.inl (by simpa [badLegal] using hL)
  have hSuccessUnion :
      μ.pr (fun ω => badLegal ω ∨ badBalls ω ∨ badHeights ω ∨ badSupport ω) ≤
        μ.pr badLegal + μ.pr badBalls + μ.pr badHeights + μ.pr badSupport := by
    calc
      _ ≤ μ.pr badLegal +
          μ.pr (fun ω => badBalls ω ∨ badHeights ω ∨ badSupport ω) :=
        FinProb.pr_union μ badLegal
          (fun ω => badBalls ω ∨ badHeights ω ∨ badSupport ω)
      _ ≤ μ.pr badLegal + (μ.pr badBalls +
          μ.pr (fun ω => badHeights ω ∨ badSupport ω)) := by
        have hu := FinProb.pr_union μ badBalls
          (fun ω => badHeights ω ∨ badSupport ω)
        nlinarith [hu]
      _ ≤ μ.pr badLegal + (μ.pr badBalls + (μ.pr badHeights + μ.pr badSupport)) :=
        by
          have hu := FinProb.pr_union μ badHeights badSupport
          nlinarith [hu]
      _ = μ.pr badLegal + μ.pr badBalls + μ.pr badHeights + μ.pr badSupport := by ring
  have hSuccessPr : μ.pr badSuccess ≤ 1 / 100 := by
    calc
      μ.pr badSuccess ≤ μ.pr (fun ω => badLegal ω ∨ badBalls ω ∨ badHeights ω ∨ badSupport ω) :=
        FinProb.pr_mono μ _ _ hSuccessCover
      _ ≤ μ.pr badLegal + μ.pr badBalls +
          μ.pr badHeights + μ.pr badSupport := hSuccessUnion
      _ ≤ Real.exp (-Real.sqrt n) + Real.exp (-Real.sqrt n) / 3 +
          (1 / 300 : ℝ) + 1 / 300 := by
        linarith [hLegalPr, hBallsPr, hHeightsPr, hSupportPr]
      _ ≤ 1 / 100 := by
        have hexp : Real.exp (-Real.sqrt (n : ℝ)) < 1 / 400 := hExpN n hnExp
        norm_num at hexp ⊢
        nlinarith
  exact ⟨hLegalPr, hSuccessPr⟩

set_option maxHeartbeats 400000

/-! ### J11 helpers (05:861–887)

Local validity at an odd role reads the selections at its even neighbours, the arrays at the selected
IDs and the prospective positions near the neighbouring sites. The transfer lemmas below are stated for
an abstract height choice, eligibility, radius and scope, so that their kernel terms do not unfold the
concrete experiment; J11 only instantiates them. -/

private theorem j11_hd_self {d : ℕ} (v : CubeVertex d) : hammingDist v v = 0 :=
  _root_.hammingDist_self v

private theorem j11_hd_root {d : ℕ} (u v : CubeVertex d) :
    hammingDist u v = _root_.hammingDist u v := rfl

private theorem j11_hitSet_congr (X : Setup5 γ K' χ n N E G) {Id : Type} (A A' : X.ArraysOn Id)
    (c : Id × X.Ty) (hc : A c = A' c) : X.hitSet A c = X.hitSet A' c := by
  funext x
  unfold Setup5.hitSet
  rw [hc]

private theorem j11_recordOf_obs_mem (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc) (σ : EvenRole5 n → Option ht.hp.Loc)
    (y : OddRole5 n) (c : ht.hp.Loc × X.Ty) (hc : c ∈ (recordOf X ht H A σ y).2.1) :
    ∃ a ∈ evenNbrs y, ∃ l, σ a = some l ∧ c = (l, X.g.evenType (X.p.J n) a.1) := by
  obtain ⟨a, ha, hc⟩ := Finset.mem_biUnion.mp hc
  cases hs : σ a with
  | none => simp [hs] at hc
  | some l => exact ⟨a, ha, l, hs, by simpa [hs] using hc⟩

private theorem j11_recordOf_ref_obs (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc) (σ : EvenRole5 n → Option ht.hp.Loc)
    (y : OddRole5 n) (c : ht.hp.Loc × X.Ty × Option X.Key)
    (hc : c ∈ (recordOf X ht H A σ y).2.2.1) : (c.1, c.2.1) ∈ (recordOf X ht H A σ y).2.1 := by
  obtain ⟨a, ha, hc⟩ := Finset.mem_biUnion.mp hc
  apply Finset.mem_biUnion.mpr
  refine ⟨a, ha, ?_⟩
  cases hs : σ a with
  | none => simp [hs] at hc
  | some l =>
    simp only [hs] at hc ⊢
    split_ifs at hc
    · rw [Finset.mem_singleton.mp hc]
      exact Finset.mem_singleton_self _
    · simp at hc

private theorem j11_recordOf_mask_obs (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc) (σ : EvenRole5 n → Option ht.hp.Loc)
    (y : OddRole5 n) (c : ht.hp.Loc × X.Ty) (M : Finset (Fin X.blockBound))
    (hc : (recordOf X ht H A σ y).2.2.2 = some (c.1, c.2, M)) :
    c ∈ (recordOf X ht H A σ y).2.1 := by
  dsimp only [recordOf] at hc ⊢
  split at hc
  · split_ifs at hc with hh
    · have ha := (Classical.choose_spec hh).1
      cases hs : σ (Classical.choose hh) with
      | none => simp [hs] at hc
      | some l =>
        simp only [hs, Option.some.injEq, Prod.mk.injEq] at hc
        apply Finset.mem_biUnion.mpr
        refine ⟨Classical.choose hh, ha, ?_⟩
        rw [hs, Finset.mem_singleton]
        exact Prod.ext hc.1.symm hc.2.1.symm
  · simp at hc

private theorem j11_recordOf_congr (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H : X.KeyHist) (A A' : X.ArraysOn ht.hp.Loc)
    (σ σ' : EvenRole5 n → Option ht.hp.Loc) (y : OddRole5 n)
    (hσ : ∀ a ∈ evenNbrs y, σ a = σ' a)
    (hA : ∀ a ∈ evenNbrs y, ∀ l, σ a = some l →
      A (l, X.g.evenType (X.p.J n) a.1) = A' (l, X.g.evenType (X.p.J n) a.1)) :
    recordOf X ht H A σ y = recordOf X ht H A' σ' y := by
  have h1 : (recordOf X ht H A σ y).2.1 = (recordOf X ht H A' σ' y).2.1 := by
    apply Finset.biUnion_congr rfl
    intro a ha
    rw [hσ a ha]
  have h2 : (recordOf X ht H A σ y).2.2.1 = (recordOf X ht H A' σ' y).2.2.1 := by
    apply Finset.biUnion_congr rfl
    intro a ha
    rw [hσ a ha]
  have h3 : (recordOf X ht H A σ y).2.2.2 = (recordOf X ht H A' σ' y).2.2.2 := by
    dsimp only [recordOf]
    split
    · have hex : (∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ a).isSome) ↔
          ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ' a).isSome := by
        constructor <;> rintro ⟨a, ha, htype, hs⟩
        · exact ⟨a, ha, htype, (hσ a ha) ▸ hs⟩
        · exact ⟨a, ha, htype, (hσ a ha).symm ▸ hs⟩
      by_cases hh : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ a).isSome
      · have hh' := hex.mp hh
        rw [dif_pos hh, dif_pos hh']
        have ha := (Classical.choose_spec hh).1
        have heq : Classical.choose hh = Classical.choose hh' := by
          congr 1
          exact funext fun a => propext (by
            by_cases ha : a ∈ evenNbrs y
            · simp only [ha, true_and, hσ a ha]
            · simp [ha])
        rw [← heq, ← hσ _ ha]
        cases hs : σ (Classical.choose hh) with
        | none => rfl
        | some l =>
          dsimp only
          rw [j11_hitSet_congr X A A' _ (hA _ ha l hs)]
      · rw [dif_neg hh, dif_neg (mt hex.mpr hh)]
    · rfl
  exact Prod.ext rfl (Prod.ext h1 (Prod.ext h2 h3))

/-- Step 3 failure reads the record's observed arrays only. -/
private theorem j11_step3Fail_congr (X : Setup5 γ K' χ n N E G) {Id : Type} [DecidableEq Id]
    (H : X.KeyHist) (r : X.RecordOn Id) (A B : X.ArraysOn Id)
    (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
    (href : ∀ c ∈ r.2.2.1, (c.1, c.2.1) ∈ r.2.1)
    (hobs : ∀ c ∈ r.2.1, A c = B c) : X.step3FailOn H r A ↔ X.step3FailOn H r B := by
  have hrefs := Lane_sol_s05_centres.refsOn_arrays_congr X H r A B href hobs
  have hgate : X.candGateOn H r A (H.2 r.1) ↔ X.candGateOn H r B (H.2 r.1) :=
    Lane_sol_s05_hist1b.candGateOn_arrays_congr X H r A B hmask hobs _
  have hmass (e : Option (Id × X.Ty × Finset (Fin X.blockBound))) :
      X.step3MassOn H r A e = X.step3MassOn H r B e :=
    Lane_sol_s05_hist1b.step3MassOn_arrays_congr X H r A B hmask hobs e
  have hcap := Lane_sol_s05_centres.highCapped_arrays_congr X H r A B hmask hobs
  have hprice := Lane_sol_s05_centres.highPrice_arrays_congr X H r A B hmask href hobs
  simp only [Setup5.step3FailOn, hgate, hmass, hrefs, hcap, hprice]

/-- The three Step 3 stars of local validity transfer along an equal record with equal observed
arrays. -/
private theorem j11_star_congr (X : Setup5 γ K' χ n N E G) {Id : Type} [DecidableEq Id]
    (H : X.KeyHist) (r r' : X.RecordOn Id) (A B : X.ArraysOn Id) (hr : r = r')
    (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
    (href : ∀ c ∈ r.2.2.1, (c.1, c.2.1) ∈ r.2.1)
    (hobs : ∀ c ∈ r.2.1, A c = B c) :
    (0 < X.step3PostOn H r A none (H.2 r.1) → 0 < X.step3PostOn H r' B none (H.2 r'.1)) ∧
    (X.candGateOn H r A (H.2 r.1) → X.candGateOn H r' B (H.2 r'.1)) ∧
    (¬ X.step3FailOn H r A → ¬ X.step3FailOn H r' B) := by
  subst hr
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [← Lane_sol_s05_centres.step3Post_arrays_congr X H r A B hmask hobs none]
    exact h
  · exact (Lane_sol_s05_hist1b.candGateOn_arrays_congr X H r A B hmask hobs _).mp h
  · rwa [← j11_step3Fail_congr X H r A B hmask href hobs]

private theorem j11_heavyCount_congr (X : Setup5 γ K' χ n N E G) {ht : X.HeightChoice5}
    (H : X.KeyHist) (ω ω' : X.CΩ ht) (v : EvenRole5 n) (c : X.CRef ht)
    (h : arr ω c.1 (X.g.evenType (X.p.J n) v.1) = arr ω' c.1 (X.g.evenType (X.p.J n) v.1)) :
    X.heavyCount H ω v c = X.heavyCount H ω' v c := by
  unfold Setup5.heavyCount
  rw [h]

private theorem j11_refSubset_congr (X : Setup5 γ K' χ n N E G) {ht : X.HeightChoice5}
    (H : X.KeyHist) (ω ω' : X.CΩ ht) (v : EvenRole5 n) (l : ht.hp.Loc)
    (h : arr ω l (X.g.evenType (X.p.J n) v.1) = arr ω' l (X.g.evenType (X.p.J n) v.1)) :
    X.refSubset H ω v l = X.refSubset H ω' v l := by
  unfold Setup5.refSubset Setup5.refSubsetOn
  rw [j11_hitSet_congr X (arraysOf ω) (arraysOf ω') (l, X.g.evenType (X.p.J n) v.1) h]

/-- The record of an odd role transfers when the neighbouring selections and the selected arrays
agree. -/
private theorem j11_record_eq (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (elig : X.CΩ ht → ht.hp.EligMap) (H : X.KeyHist) (ω ω' : X.CΩ ht) (R : ℕ) (y : OddRole5 n)
    (hsel : ∀ a ∈ evenNbrs y, X.selAt elig ω R a = X.selAt elig ω' R a)
    (harr : ∀ a ∈ evenNbrs y, ∀ l, X.selAt elig ω R a = some l → ∀ K,
      arr ω l K = arr ω' l K) :
    X.actualRecordAt elig H ω R y = X.actualRecordAt elig H ω' R y := by
  rw [actualRecordAt_eq X ht elig H ω R y, actualRecordAt_eq X ht elig H ω' R y]
  exact j11_recordOf_congr X ht H _ _ _ _ y hsel (fun a ha l hl => harr a ha l hl _)

/-- Transfer of local validity for an abstract height choice and eligibility. -/
private theorem j11_valid_transfer (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (elig : X.KeyHist → X.CΩ ht → ht.hp.EligMap) (H : X.KeyHist) (ω ω' : X.CΩ ht) (R : ℕ)
    (y : OddRole5 n)
    (hsel : ∀ a ∈ evenNbrs y, X.selAt (elig H) ω R a = X.selAt (elig H) ω' R a)
    (harr : ∀ a ∈ evenNbrs y, ∀ l, X.selAt (elig H) ω R a = some l → ∀ K,
      arr ω l K = arr ω' l K)
    (hpos : ∀ a ∈ evenNbrs y, ∀ (j : Fin (ht.hp.H + 1)) (u : CubeVertex ht.hp.d),
      hammingDist u (X.siteOf a) ≤ ht.hp.r → pos ω (u, j) = pos ω' (u, j))
    (hv : X.LocalValidAt ht elig H ω R y) : X.LocalValidAt ht elig H ω' R y := by
  have hrec := j11_record_eq X ht (elig H) H ω ω' R y hsel harr
  have hobs (c : ht.hp.Loc × X.Ty) (hc : c ∈ (X.actualRecordAt (elig H) H ω R y).2.1) :
      arraysOf ω c = arraysOf ω' c := by
    rw [actualRecordAt_eq] at hc
    obtain ⟨a, ha, l, hl, rfl⟩ := j11_recordOf_obs_mem X ht H _ _ y c hc
    exact harr a ha l hl _
  have hmask (c : ht.hp.Loc × X.Ty) (M : Finset (Fin X.blockBound))
      (hc : (X.actualRecordAt (elig H) H ω R y).2.2.2 = some (c.1, c.2, M)) :
      c ∈ (X.actualRecordAt (elig H) H ω R y).2.1 := by
    rw [actualRecordAt_eq] at hc ⊢
    exact j11_recordOf_mask_obs X ht H _ _ y c M hc
  have href (c : ht.hp.Loc × X.Ty × Option X.Key)
      (hc : c ∈ (X.actualRecordAt (elig H) H ω R y).2.2.1) :
      (c.1, c.2.1) ∈ (X.actualRecordAt (elig H) H ω R y).2.1 := by
    rw [actualRecordAt_eq] at hc ⊢
    exact j11_recordOf_ref_obs X ht H _ _ y c hc
  have hstar := j11_star_congr X H _ _ (arraysOf ω) (arraysOf ω') hrec hmask href hobs
  obtain ⟨hbase, hstep1, hs, hcounts, hT, hhits, hheavy, hblock, hpath, hgate, hfail⟩ := hv
  refine ⟨hbase, hstep1, ?_, ?_, ?_, ?_, ?_, ?_, hstar.1 hpath, hstar.2.1 hgate, hstar.2.2 hfail⟩
  · intro a ha
    rw [← hsel a ha]
    exact hs a ha
  · intro a ha j
    have hfil : (Finset.univ.filter fun u : CubeVertex ht.hp.d =>
          pos ω' (u, j) = true ∧ hammingDist u (X.siteOf a) ≤ ht.hp.r) =
        (Finset.univ.filter fun u : CubeVertex ht.hp.d =>
          pos ω (u, j) = true ∧ hammingDist u (X.siteOf a) ≤ ht.hp.r) :=
      Lane_opus_s05_j11.filter_congr' fun u _ =>
        ⟨fun h => ⟨(hpos a ha j u h.2).trans h.1, h.2⟩,
          fun h => ⟨(hpos a ha j u h.2).symm.trans h.1, h.2⟩⟩
    rw [hfil]
    exact hcounts a ha j
  · have himg : (evenNbrs y).image (fun a => X.selAt (elig H) ω' R a) =
        (evenNbrs y).image (fun a => X.selAt (elig H) ω R a) := by
      apply Finset.image_congr
      intro a ha
      exact (hsel a ha).symm
    rw [himg]
    exact hT
  · intro a ha l k hl hk
    have hl0 : X.selAt (elig H) ω R a = some l := (hsel a ha).trans hl
    have hh := hhits a ha l k hl0 hk
    rwa [j11_hitSet_congr X (arraysOf ω) (arraysOf ω') (l, X.g.evenType (X.p.J n) a.1)
      (harr a ha l hl0 _)] at hh
  · intro a ha l hl
    have hl0 : X.selAt (elig H) ω R a = some l := (hsel a ha).trans hl
    have he := harr a ha l hl0 (X.g.evenType (X.p.J n) a.1)
    have hh := hheavy a ha l hl0
    show (X.heavyCount H ω' a (l, X.refSubset H ω' a l) : ℝ) ≤
      X.p.nu0 * (X.refLen (X.g.evenType (X.p.J n) a.1) (X.refSubset H ω' a l) : ℝ)
    rw [← j11_refSubset_congr X H ω ω' a l he,
      ← j11_heavyCount_congr X H ω ω' a (l, X.refSubset H ω a l) he]
    exact hh
  · intro c hc i
    rw [← hrec] at hc
    rw [← hobs c hc]
    exact hblock c hc i

/-- Local position count: a vertex within `r` of a neighbouring site lies in the scope. -/
private theorem j11_scope (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5) (y : OddRole5 n)
    (R slack : ℕ)
    (hgap : ∀ a ∈ evenNbrs y,
      hammingDist (X.siteOf a) (X.St.oneHot (X.St.stateOf y.1)) + R + 16 ≤ slack)
    (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (u : CubeVertex ht.hp.d)
    (hu : hammingDist u (X.siteOf a) ≤ R) (l : ht.hp.Loc) (hl : hammingDist l.1 u ≤ ht.hp.r + 16) :
    l ∈ X.scopeBall (h := ht) y.1 (ht.hp.r + slack) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have h1 := HypercubeRamsey.hammingDist_triangle l.1 u (X.St.oneHot (X.St.stateOf y.1))
  have h2 := HypercubeRamsey.hammingDist_triangle u (X.siteOf a) (X.St.oneHot (X.St.stateOf y.1))
  have h3 : @HypercubeRamsey.hammingDist ht.hp.d (X.siteOf a) (X.St.oneHot (X.St.stateOf y.1)) +
      R + 16 ≤ slack := hgap a ha
  omega

/-- Generic J11: local validity reads the scope when the scope contains the `(r+16)`-balls around
the `R`-balls of the neighbouring sites and eligibility is local and shaped. -/
private theorem j11_local_generic (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (elig : X.KeyHist → X.CΩ ht → ht.hp.EligMap) (H : X.KeyHist) (y : OddRole5 n) (R : ℕ)
    (S : Finset ht.hp.Loc) (hD : ht.hp.D ≤ 16)
    (hscope : ∀ a ∈ evenNbrs y, ∀ u : CubeVertex ht.hp.d, hammingDist u (X.siteOf a) ≤ R →
      ∀ l : ht.hp.Loc, hammingDist l.1 u ≤ ht.hp.r + 16 → l ∈ S)
    (hloc : ∀ s j, FinProb.DependsOn (fun ω : X.CΩ ht => elig H ω s j)
      (Finset.univ.filter fun l : ht.hp.Loc => hammingDist l.1 s ≤ ht.hp.r + 16))
    (hshape : ∀ ω s j l, l ∈ elig H ω s j → hammingDist l.1 s ≤ ht.hp.r) :
    FinProb.DependsOn (fun ω => X.LocalValidAt ht elig H ω R y) S := by
  intro ω ω' hagree
  have hE (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (u : CubeVertex ht.hp.d)
      (hu : hammingDist u (X.siteOf a) ≤ R) (j : Fin (ht.hp.H + 1)) :
      elig H ω u j = elig H ω' u j :=
    hloc u j ω ω' fun l hl => hagree l (hscope a ha u hu l (Finset.mem_filter.mp hl).2)
  have hactE (ξ : X.CΩ ht) (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (u : CubeVertex ht.hp.d)
      (hu : hammingDist u (X.siteOf a) ≤ R) (j : Fin (ht.hp.H + 1)) (l : ht.hp.Loc)
      (hl : l ∈ elig H ξ u j) : l ∈ S := by
    have := hshape ξ u j l hl
    exact hscope a ha u hu l (by omega)
  have hbad (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (u : CubeVertex ht.hp.d)
      (hu : _root_.hammingDist u (X.siteOf a) ≤ R) (j : Fin (ht.hp.H + 1)) :
      ht.hp.Bad (pos ω) (act ω) (elig H ω) u j ↔ ht.hp.Bad (pos ω') (act ω') (elig H ω') u j := by
    have hu' : hammingDist u (X.siteOf a) ≤ R := hu
    apply Lane_opus_s05_j11.bad_congr ht.hp _ _ _ _ _ _ u j (hE a ha u hu' j)
    · intro l hl
      exact congrArg (fun z => z.2.1) (hagree l (hactE ω a ha u hu' j l hl))
    · intro w hw
      have hw' : hammingDist w u ≤ ht.hp.r + 16 := by
        rw [j11_hd_root]
        omega
      have e := hagree (w, j) (hscope a ha u hu' (w, j) hw')
      exact ⟨congrArg Prod.fst e, congrArg (fun z => z.2.1) e⟩
  have h0 (a : EvenRole5 n) : hammingDist (X.siteOf a : CubeVertex ht.hp.d) (X.siteOf a) ≤ R := by
    rw [j11_hd_self]
    exact Nat.zero_le _
  have hsel (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
      X.selAt (elig H) ω R a = X.selAt (elig H) ω' R a := by
    refine Lane_opus_s05_j11.selectionAt_congr ht.hp (X.sites ht) (pos ω) (act ω) (pos ω')
      (act ω') (elig H ω) (elig H ω') (tie ω) (tie ω') R (X.siteOf a) (hbad a ha)
      (fun j => hE a ha _ (h0 a) j) ?_ ?_
    · intro j l hl
      exact congrArg (fun z => z.2.1) (hagree l (hactE ω a ha _ (h0 a) j l hl))
    · intro j
      have hl : hammingDist (X.siteOf a, j).1 (X.siteOf a : CubeVertex ht.hp.d) ≤ ht.hp.r + 16 := by
        show hammingDist (X.siteOf a : CubeVertex ht.hp.d) (X.siteOf a) ≤ ht.hp.r + 16
        rw [j11_hd_self]
        exact Nat.zero_le _
      exact congrArg (fun z => z.2.2.1) (hagree (X.siteOf a, j) (hscope a ha _ (h0 a) _ hl))
  have hselS (ξ : X.CΩ ht) (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (l : ht.hp.Loc)
      (hl : X.selAt (elig H) ξ R a = some l) : l ∈ S := by
    obtain ⟨j, hj⟩ := Lane_opus_s05_j11.selectionAt_mem ht.hp (X.sites ht) (pos ξ) (act ξ)
      (elig H ξ) (tie ξ) R (X.siteOf a) l hl
    exact hactE ξ a ha _ (h0 a) j l hj
  have hpos (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (j : Fin (ht.hp.H + 1))
      (u : CubeVertex ht.hp.d) (hu : hammingDist u (X.siteOf a) ≤ ht.hp.r) :
      pos ω (u, j) = pos ω' (u, j) := by
    have hl : hammingDist (u, j).1 (X.siteOf a : CubeVertex ht.hp.d) ≤ ht.hp.r + 16 := by
      show hammingDist u (X.siteOf a : CubeVertex ht.hp.d) ≤ ht.hp.r + 16
      omega
    exact congrArg Prod.fst (hagree (u, j) (hscope a ha _ (h0 a) (u, j) hl))
  have harr (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (l : ht.hp.Loc)
      (hl : X.selAt (elig H) ω R a = some l) (K : X.Ty) : arr ω l K = arr ω' l K :=
    congrArg (fun z => z.2.2.2 K) (hagree l (hselS ω a ha l hl))
  show X.LocalValidAt ht elig H ω R y = X.LocalValidAt ht elig H ω' R y
  exact propext ⟨j11_valid_transfer X ht elig H ω ω' R y hsel harr hpos,
    j11_valid_transfer X ht elig H ω' ω R y (fun a ha => (hsel a ha).symm)
      (fun a ha l hl K => (harr a ha l ((hsel a ha).trans hl) K).symm)
      (fun a ha j u hu => (hpos a ha j u hu).symm)⟩

/-- The neighbouring sites and the long radius fit the canonical slack (05:309–312). -/
private theorem j11_gap (X : Setup5 γ K' χ n N E G) (y : OddRole5 n) (a : EvenRole5 n)
    (ha : a ∈ evenNbrs y) :
    hammingDist (X.siteOf a) (X.St.oneHot (X.St.stateOf y.1)) + (canonHt X).hp.Rlong + 16 ≤
      Lane_sol_s05_centres.centreSlack X.p n := by
  have hadj : (cube n).Adj a.1 y.1 := (Finset.mem_filter.mp ha).2
  have hdist : (hammingDist (X.siteOf a) (X.St.oneHot (X.St.stateOf y.1)) : ℝ) ≤
      4 * (n : ℝ) ^ (1 / 2 : ℝ) + 302 :=
    Lane_sol_s05_centres.adjacent_embedding_upper X.St a.1 y.1 hadj
  have hslack := Lane_sol_s05_centres.centreSlack_scope X.p n
  have hR : (canonHt X).hp.Rlong = 16 * topScale n (X.p.alpha / 1000000) (X.p.alpha / 100000) := by
    show 2 * 8 * topScale n (X.p.alpha / 1000000) (X.p.alpha / 100000) = _
    ring
  rw [hR]
  have hgapR : ((hammingDist (X.siteOf a) (X.St.oneHot (X.St.stateOf y.1)) +
      16 * topScale n (X.p.alpha / 1000000) (X.p.alpha / 100000) + 16 : ℕ) : ℝ) ≤
      (Lane_sol_s05_centres.centreSlack X.p n : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hgapR

/-- SUB-LEMMA J11 (05:880–887): local validity at the long radius reads center data within
`r + centreSlack`: neighbouring sites lie within `4√n + 302` of the odd image
(`Lane_sol_s05_centres.adjacent_embedding_upper`), selections read `Rlong + r + 16` around them
(`markElig_local`), and `centreSlack_scope` absorbs both. -/
theorem localValid_local (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (y : OddRole5 n) :
    FinProb.DependsOn (fun ω => X.LocalValidAt (canonHt X) (markElig X (canonHt X)) H ω (canonHt X).hp.Rlong y)
      (X.scopeBall (h := canonHt X) y.1 ((canonHt X).hp.r + Lane_sol_s05_centres.centreSlack X.p n)) :=
  j11_local_generic X (canonHt X) (markElig X (canonHt X)) H y (canonHt X).hp.Rlong _
    (by show 8 ≤ 16; norm_num)
    (j11_scope X (canonHt X) y (canonHt X).hp.Rlong _ (j11_gap X y))
    (markElig_local X (canonHt X) H)
    (fun ω s j l hl => (markElig_shape X (canonHt X) H ω s j l hl).2.2)

set_option maxHeartbeats 400000

/-- The short presentation mass for a given height choice and eligibility (as in
`shortPresentationMass`). -/
def shortPresMassOf (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (elig : X.KeyHist → X.CΩ ht → ht.hp.EligMap) (H : X.KeyHist) (y : OddRole5 n)
    (r : X.RecordOn ht.hp.Loc) (a : X.ArraysOn ht.hp.Loc) : ℝ :=
  (X.centreLaw ht H).pr fun ω =>
    X.LocalValidAt ht elig H ω (ht.hp.Rshort (X.p.m n)) y ∧
    X.actualRecordAt (elig H) H ω (ht.hp.Rshort (X.p.m n)) y = r ∧
    ∀ c ∈ r.2.1, arraysOf ω c = a c

/-! ### J12 helpers: the short presentation reads only near keys and arrays

The record, eligibility, selections and star tests at an odd role `y` read keys and arrays of types
whose low keys lie within sign distance `R + 4` of `sign y`, where `R` is the consultation radius;
unread arrays are integrated out by masking them (05:991–1001). -/

section J12

open Lane_opus_s05_j12

/-- `Finset.mem_filter` for whatever decidability instance the filter carries (definitions over
`ht.hp.Loc` and `CubeVertex ht.hp.d` may carry `Classical.propDecidable`). -/
private theorem j12_mem_filter {α : Type*} {p : α → Prop} {inst : DecidablePred p} {s : Finset α}
    {a : α} (h : a ∈ @Finset.filter α p inst s) : a ∈ s ∧ p a := by
  letI := inst
  exact Finset.mem_filter.mp h

/-- `Finset.filter_congr` for arbitrary decidability instances on both sides. -/
private theorem j12_filter_congr {α : Type*} {p q : α → Prop} {ip : DecidablePred p}
    {iq : DecidablePred q} {s : Finset α} (h : ∀ x ∈ s, p x ↔ q x) :
    @Finset.filter α p ip s = @Finset.filter α q iq s := by
  letI := ip
  letI := iq
  exact Finset.filter_congr h

private theorem j12_recordOf_congr (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H H' : X.KeyHist) (A A' : X.ArraysOn ht.hp.Loc)
    (σ σ' : EvenRole5 n → Option ht.hp.Loc) (y : OddRole5 n)
    (hσ : ∀ a ∈ evenNbrs y, σ a = σ' a)
    (hA : ∀ a ∈ evenNbrs y, ∀ l, A (l, X.g.evenType (X.p.J n) a.1) =
      A' (l, X.g.evenType (X.p.J n) a.1))
    (htarget : H.2 (X.g.roleKey (X.p.J n) y.1) = H'.2 (X.g.roleKey (X.p.J n) y.1)) :
    recordOf X ht H A σ y = recordOf X ht H' A' σ' y := by
  have hobs : (evenNbrs y).biUnion (fun a => match σ a with
      | some l => {(l, X.g.evenType (X.p.J n) a.1)} | none => ∅) =
      (evenNbrs y).biUnion (fun a => match σ' a with
      | some l => {(l, X.g.evenType (X.p.J n) a.1)} | none => ∅) := by
    apply Finset.biUnion_congr rfl
    intro a ha
    rw [hσ a ha]
  have href : (evenNbrs y).biUnion (fun a => match σ a with
      | some l => if X.g.roleKey (X.p.J n) y.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          (X.g.roleKey (X.p.J n) y.1).isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome then
          {(l, X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)} else ∅
      | none => ∅) =
      (evenNbrs y).biUnion (fun a => match σ' a with
      | some l => if X.g.roleKey (X.p.J n) y.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          (X.g.roleKey (X.p.J n) y.1).isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome then
          {(l, X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)} else ∅
      | none => ∅) := by
    apply Finset.biUnion_congr rfl
    intro a ha
    rw [hσ a ha]
  dsimp only [recordOf]
  rw [hobs, href]
  congr 1
  split
  · next k hk =>
      have ht' : X.lowCol H.2 k = X.lowCol H'.2 k := by
        have he := htarget
        rw [hk] at he
        exact congrFun he ⟨0, by simp [colLen5]⟩
      have hex : (∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ a).isSome) ↔
          ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ' a).isSome := by
        constructor <;> rintro ⟨a, ha, htype, hs⟩
        · exact ⟨a, ha, htype, (hσ a ha) ▸ hs⟩
        · exact ⟨a, ha, htype, (hσ a ha).symm ▸ hs⟩
      by_cases hh : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ a).isSome
      · have hh' := hex.mp hh
        rw [dif_pos hh, dif_pos hh']
        have ha := (Classical.choose_spec hh).1
        have heq : Classical.choose hh = Classical.choose hh' := by
          congr 1
          exact funext fun a => propext (by
            by_cases ha : a ∈ evenNbrs y
            · simp only [ha, true_and, hσ a ha]
            · simp [ha])
        rw [← heq, ← hσ _ ha]
        cases hs : σ (Classical.choose hh) with
        | none => rfl
        | some l =>
          dsimp only
          have hhit : X.hitSet A (l, X.g.evenType (X.p.J n) (Classical.choose hh).1) (X.lowCol H.2 k) =
              X.hitSet A' (l, X.g.evenType (X.p.J n) (Classical.choose hh).1) (X.lowCol H'.2 k) := by
            simp only [Setup5.hitSet, hA _ ha l, ht']
          rw [hhit]
      · rw [dif_neg hh, dif_neg (mt hex.mpr hh)]
  · rfl

private theorem j12_recordOf_obs_type (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc)
    (σ : EvenRole5 n → Option ht.hp.Loc) (y : OddRole5 n) (c)
    (hc : c ∈ (recordOf X ht H A σ y).2.1) :
    ∃ a ∈ evenNbrs y, c.2 = X.g.evenType (X.p.J n) a.1 := by
  obtain ⟨a, ha, hc⟩ := Finset.mem_biUnion.mp hc
  cases hs : σ a with
  | none => simp [hs] at hc
  | some l =>
    have he : c = (l, X.g.evenType (X.p.J n) a.1) := by simpa [hs] using hc
    exact ⟨a, ha, congrArg Prod.snd he⟩

private theorem j12_recordOf_ref_type (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc)
    (σ : EvenRole5 n → Option ht.hp.Loc) (y : OddRole5 n) (c)
    (hc : c ∈ (recordOf X ht H A σ y).2.2.1) :
    ∃ a ∈ evenNbrs y, c.2.1 = X.g.evenType (X.p.J n) a.1 ∧
      c.2.2 = X.g.optionalKey (X.p.J n) a.1 := by
  obtain ⟨a, ha, hc⟩ := Finset.mem_biUnion.mp hc
  cases hs : σ a with
  | none => simp [hs] at hc
  | some l =>
    simp only [hs] at hc
    split_ifs at hc with hh
    · have he := Finset.mem_singleton.mp hc
      exact ⟨a, ha, congrArg (fun c => c.2.1) he, congrArg (fun c => c.2.2) he⟩
    · simp at hc

private theorem j12_recordOf_mask_type (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc)
    (σ : EvenRole5 n → Option ht.hp.Loc) (y : OddRole5 n) (c : ht.hp.Loc × X.Ty)
    (M : Finset (Fin X.blockBound))
    (hc : (recordOf X ht H A σ y).2.2.2 = some (c.1, c.2, M)) :
    ∃ a ∈ evenNbrs y, c.2 = X.g.evenType (X.p.J n) a.1 := by
  dsimp only [recordOf] at hc
  split at hc
  · split_ifs at hc with hh
    · have ha := (Classical.choose_spec hh).1
      cases hs : σ (Classical.choose hh) with
      | none => simp [hs] at hc
      | some l =>
        simp only [hs, Option.some.injEq, Prod.mk.injEq] at hc
        exact ⟨Classical.choose hh, ha, hc.2.1.symm⟩
  · simp at hc

private theorem j12_recordOf_data (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc)
    (σ : EvenRole5 n → Option ht.hp.Loc) (y : OddRole5 n)
    {t : CubeVertex (X.p.m n)} {q : ℕ}
    (htarget : within X t q (X.g.roleKey (X.p.J n) y.1))
    (htypes : ∀ a ∈ evenNbrs y, ∀ ℓ ∈ (X.g.evenType (X.p.J n) a.1).2.1, within X t q ℓ)
    (hopts : ∀ a ∈ evenNbrs y, ∀ ℓ ∈ (X.g.optionalKey (X.p.J n) a.1).toFinset, within X t q ℓ) :
    (∀ ℓ ∈ recordKeys X (recordOf X ht H A σ y), within X t q ℓ) ∧
    (∀ c ∈ recordArrays X (recordOf X ht H A σ y),
      ∃ a ∈ evenNbrs y, c.2 = X.g.evenType (X.p.J n) a.1) := by
  have har : ∀ c ∈ recordArrays X (recordOf X ht H A σ y),
      ∃ a ∈ evenNbrs y, c.2 = X.g.evenType (X.p.J n) a.1 := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · rcases Finset.mem_union.mp hc with hc | hc
      · exact j12_recordOf_obs_type X ht H A σ y c hc
      · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨a, ha, htype, _⟩ := j12_recordOf_ref_type X ht H A σ y d hd
        exact ⟨a, ha, htype⟩
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      have hd' : (recordOf X ht H A σ y).2.2.2 = some d := by simpa using hd
      exact j12_recordOf_mask_type X ht H A σ y (d.1, d.2.1) d.2.2 hd'
  refine ⟨?_, har⟩
  intro ℓ hℓ
  rcases Finset.mem_insert.mp hℓ with hℓ | hℓ
  · exact hℓ ▸ htarget
  · rcases Finset.mem_union.mp hℓ with hℓ | hℓ
    · obtain ⟨c, hc, hℓ⟩ := Finset.mem_biUnion.mp hℓ
      obtain ⟨a, ha, he⟩ := har c hc
      exact htypes a ha ℓ (he ▸ hℓ)
    · obtain ⟨c, hc, hℓ⟩ := Finset.mem_biUnion.mp hℓ
      obtain ⟨a, ha, _, hopt⟩ := j12_recordOf_ref_type X ht H A σ y c hc
      exact hopts a ha ℓ (hopt ▸ hℓ)

private theorem j12_singleton_congr (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H H' : X.KeyHist) (A A' : X.ArraysOn ht.hp.Loc)
    (v : EvenRole5 n) (l : ht.hp.Loc) (hb : H.1 = H'.1)
    (hc : ∀ ℓ ∈ (X.g.evenType (X.p.J n) v.1).2.1, H.2 ℓ = H'.2 ℓ)
    (ho : ∀ ℓ ∈ (X.g.optionalKey (X.p.J n) v.1).toFinset, H.2 ℓ = H'.2 ℓ)
    (ha : A (l, X.g.evenType (X.p.J n) v.1) = A' (l, X.g.evenType (X.p.J n) v.1)) :
    singletonOK X ht H A v l = singletonOK X ht H' A' v l := by
  have hlaw : X.blockLaw H (X.g.evenType (X.p.J n) v.1) =
      X.blockLaw H' (X.g.evenType (X.p.J n) v.1) := blockLawOn_ext X H H' _ _ hb hc
  have havg (x) : X.avgMarg H (X.g.evenType (X.p.J n) v.1) x =
      X.avgMarg H' (X.g.evenType (X.p.J n) v.1) x := by simp only [avgMarg, hlaw]
  have hsub := refSubset_ext X H H' A A' (l, X.g.evenType (X.p.J n) v.1)
    (X.g.optionalKey (X.p.J n) v.1) ha ho
  have hh : heavyCountOn X ht H A v (l, X.refSubsetOn H A
      (l, X.g.evenType (X.p.J n) v.1) (X.g.optionalKey (X.p.J n) v.1)) =
      heavyCountOn X ht H' A' v (l, X.refSubsetOn H' A'
      (l, X.g.evenType (X.p.J n) v.1) (X.g.optionalKey (X.p.J n) v.1)) := by
    simp only [heavyCountOn, hsub, ha, PriorHeavy, havg]
    try rfl
  have hhit (k) (hk : X.g.optionalKey (X.p.J n) v.1 = some (.inl k)) :
      X.hitSet A (l, X.g.evenType (X.p.J n) v.1) (X.lowCol H.2 k) =
      X.hitSet A' (l, X.g.evenType (X.p.J n) v.1) (X.lowCol H'.2 k) := by
    have he := ho (.inl k) (by simp [hk])
    simp only [Setup5.hitSet, Setup5.lowCol, ha, he]
    try rfl
  dsimp only [singletonOK]
  rw [hh, hsub]
  congr 1
  apply propext
  constructor <;> intro h k hk
  · simpa only [hhit k hk] using h k hk
  · simpa only [hhit k hk] using h k hk

private theorem j12_failSets_congr (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H H' : X.KeyHist) (P : ht.hp.Loc → Bool)
    (A A' : X.ArraysOn ht.hp.Loc) (b : X.St.Site) (j : ℕ)
    (v : EvenRole5 n) (hv : X.St.stateOf v.1 ∈ X.St.neighbors b)
    {t : CubeVertex (X.p.m n)} {q₀ q : ℕ}
    (hnear : _root_.hammingDist (X.g.sign v.1) t ≤ q₀) (hq : q₀ + 3 ≤ q)
    (hb : H.1 = H'.1) (hc : ∀ ℓ, within X t q ℓ → H.2 ℓ = H'.2 ℓ)
    (ha : ∀ c, c.2 ∈ localTypes X t q → A c = A' c) :
    failSets X ht H P A b j = failSets X ht H' P A' b j := by
  have hynear (y : OddRole5 n) (hy : X.St.stateOf y.1 = b) :
      _root_.hammingDist (X.g.sign y.1) t ≤ q₀ + 1 := by
    have h1 := incident_sign X v b hv y hy
    have h2 := _root_.hammingDist_triangle (X.g.sign y.1) (X.g.sign v.1) t
    omega
  have hfail (μ : X.St.Site → ht.hp.Loc) (y : OddRole5 n) (hy : X.St.stateOf y.1 = b) :
      X.step3FailOn H (recordOf X ht H A (fun a => some (μ (X.St.stateOf a.1))) y) A =
      X.step3FailOn H' (recordOf X ht H' A' (fun a => some (μ (X.St.stateOf a.1))) y) A' := by
    have hty (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
        X.g.evenType (X.p.J n) a.1 ∈ localTypes X t q := by
      simp only [localTypes, Finset.mem_filter, Finset.mem_univ, true_and]
      intro ℓ hℓ
      have h := type_keys_within X a.1 t (q₀ + 2)
        (neighbor_sign_bound X y a ha t (q₀ + 1) (hynear y hy)) ℓ hℓ
      exact within_mono X (by omega) h
    have htarg : within X t q (X.g.roleKey (X.p.J n) y.1) := by
      have h := role_key_within X y.1 t (q₀ + 1) (hynear y hy)
      exact within_mono X (by omega) h
    have hop (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
        ∀ ℓ ∈ (X.g.optionalKey (X.p.J n) a.1).toFinset, within X t q ℓ := by
      intro ℓ hℓ
      have h := optional_key_within X a.1 t (q₀ + 2)
        (neighbor_sign_bound X y a ha t (q₀ + 1) (hynear y hy)) ℓ hℓ
      exact within_mono X (by omega) h
    have hr := j12_recordOf_congr X ht H H' A A'
      (fun a => some (μ (X.St.stateOf a.1))) (fun a => some (μ (X.St.stateOf a.1))) y
      (fun _ _ => rfl) (fun a ha' _ => ha _ (hty a ha')) (hc _ htarg)
    rw [← hr]
    have hd := j12_recordOf_data X ht H A (fun a => some (μ (X.St.stateOf a.1))) y
      htarg (fun a ha' ℓ hℓ => (Finset.mem_filter.mp (hty a ha')).2 ℓ hℓ) hop
    exact (record_tests_ext X H H' _ A A' hb (fun ℓ hℓ => hc ℓ (hd.1 ℓ hℓ))
      (fun c hc' => by
        obtain ⟨a, ha', he⟩ := hd.2 c hc'
        exact ha c (he.symm ▸ hty a ha'))).1
  unfold failSets
  congr 1
  apply Finset.filter_congr
  intro μ _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  exact exists_congr fun y => and_congr_right (fun hy => by rw [hfail μ y hy])

private theorem j12_eligOf_congr (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H H' : X.KeyHist) (P : ht.hp.Loc → Bool)
    (A A' : X.ArraysOn ht.hp.Loc) (v : EvenRole5 n)
    {t : CubeVertex (X.p.m n)} {q₀ q : ℕ}
    (hnear : _root_.hammingDist (X.g.sign v.1) t ≤ q₀) (hq : q₀ + 3 ≤ q)
    (hb : H.1 = H'.1) (hc : ∀ ℓ, within X t q ℓ → H.2 ℓ = H'.2 ℓ)
    (ha : ∀ c, c.2 ∈ localTypes X t q → A c = A' c) :
    eligOf X ht H P A (X.siteOf v) = eligOf X ht H' P A' (X.siteOf v) := by
  have hsame (w : EvenRole5 n) (hw : X.siteOf w = X.siteOf v) :
      _root_.hammingDist (X.g.sign w.1) t ≤ q₀ := by
    have he : X.St.stateOf w.1 = X.St.stateOf v.1 := X.St.oneHot_injective hw
    rw [(X.St.state_determines w.1 v.1 he).2.1]
    exact hnear
  have hs (w : EvenRole5 n) (hw : X.siteOf w = X.siteOf v) (l) :
      singletonOK X ht H A w l = singletonOK X ht H' A' w l := by
    have hk := type_keys_within X w.1 t q₀ (hsame w hw)
    have hm : X.g.evenType (X.p.J n) w.1 ∈ localTypes X t q := by
      simp only [localTypes, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun ℓ hℓ => within_mono X (by omega) (hk ℓ hℓ)
    exact j12_singleton_congr X ht H H' A A' w l hb
      (fun ℓ hℓ => hc ℓ (within_mono X (by omega) (hk ℓ hℓ)))
      (fun ℓ hℓ => hc ℓ (within_mono X (by omega)
        (optional_key_within X w.1 t q₀ (hsame w hw) ℓ hℓ))) (ha _ hm)
  have hmark (j : ℕ) : marks X ht H P A (X.siteOf v) j = marks X ht H' P A' (X.siteOf v) j := by
    unfold marks
    apply congrArg (fun S : Finset ht.hp.Loc => S.filter (fun l => (l.2 : ℕ) = j))
    apply Finset.biUnion_congr rfl
    intro b hb'
    obtain ⟨u, hu, he⟩ := (j12_mem_filter hb').2
    have he' : u = X.St.stateOf v.1 := X.St.oneHot_injective he
    have hv : X.St.stateOf v.1 ∈ X.St.neighbors b := he' ▸ hu
    apply Finset.biUnion_congr rfl
    intro j' _
    exact congrArg (fun F : Finset (Finset ht.hp.Loc) =>
      (Lane_sol_s05_centres.markingFamily F).biUnion id)
        (j12_failSets_congr X ht H H' P A A' b j' v hv hnear hq hb hc ha)
  funext j
  unfold eligOf
  apply j12_filter_congr
  intro l _
  rw [hmark]
  apply and_congr_left
  intro _
  exact forall_congr' fun w => imp_congr_right (fun hw => by rw [hs w hw l])

/-- Mask the arrays of types outside `U` at every location. -/
private def j12_maskTie (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5) (U : Finset X.Ty)
    (v : ht.hp.TiePerm × (∀ K : X.Ty, X.Array K)) : ht.hp.TiePerm × (∀ K : X.Ty, X.Array K) :=
  (v.1, maskArrays X U v.2)

private def j12_maskAct (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5) (U : Finset X.Ty)
    (v : Bool × ht.hp.TiePerm × (∀ K : X.Ty, X.Array K)) :
    Bool × ht.hp.TiePerm × (∀ K : X.Ty, X.Array K) :=
  (v.1, j12_maskTie X ht U v.2)

private def j12_maskVal (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5) (U : Finset X.Ty)
    (v : X.CVal ht) : X.CVal ht :=
  (v.1, j12_maskAct X ht U v.2)

private def j12_maskΩ (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5) (U : Finset X.Ty)
    (ω : X.CΩ ht) : X.CΩ ht :=
  fun l => j12_maskVal X ht U (ω l)

private theorem j12_masked_law (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H H' : X.KeyHist) (t : CubeVertex (X.p.m n)) (q : ℕ)
    (hb : H.1 = H'.1) (hc : ∀ ℓ, within X t q ℓ → H.2 ℓ = H'.2 ℓ) :
    FinProb.map (X.centreLaw ht H) (j12_maskΩ X ht (localTypes X t q)) =
    FinProb.map (X.centreLaw ht H') (j12_maskΩ X ht (localTypes X t q)) := by
  unfold centreLaw j12_maskΩ
  rw [map_pi, map_pi]
  congr 1
  funext l
  unfold j12_maskVal
  rw [map_prod_snd, map_prod_snd]
  congr 1
  unfold j12_maskAct
  rw [map_prod_snd, map_prod_snd]
  congr 1
  unfold j12_maskTie
  rw [map_prod_snd, map_prod_snd]
  congr 1
  unfold maskArrays
  rw [map_pi _ (fun K (A : X.Array K) => if K ∈ localTypes X t q then A else fun _ => X.fallbackBlock K),
    map_pi _ (fun K (A : X.Array K) => if K ∈ localTypes X t q then A else fun _ => X.fallbackBlock K)]
  congr 1
  funext K
  by_cases hK : K ∈ localTypes X t q
  · simp only [hK, if_true]
    have hcol : ∀ ℓ ∈ K.2.1, H.2 ℓ = H'.2 ℓ :=
      fun ℓ hℓ => hc ℓ ((Finset.mem_filter.mp hK).2 ℓ hℓ)
    have hlaw : X.blockLaw H K = X.blockLaw H' K := blockLawOn_ext X H H' K K.2.1 hb hcol
    rw [hlaw]
  · simp only [hK, if_false]
    exact map_const _ _ _

private theorem j12_selections_congr (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H H' : X.KeyHist) (ω ω' : X.CΩ ht) (y : OddRole5 n) (R q : ℕ)
    (hq : R + 4 ≤ q) (hb : H.1 = H'.1)
    (hc : ∀ ℓ, within X (X.g.sign y.1) q ℓ → H.2 ℓ = H'.2 ℓ)
    (hp' : pos ω = pos ω') (ha' : act ω = act ω') (ht' : tie ω = tie ω')
    (hA : ∀ c, c.2 ∈ localTypes X (X.g.sign y.1) q → arraysOf ω c = arraysOf ω' c) :
    ∀ a ∈ evenNbrs y, X.selAt (markElig X ht H) ω R a = X.selAt (markElig X ht H') ω' R a := by
  intro a ha
  unfold selAt
  rw [hp', ha', ht']
  apply selection_congr
  · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  · intro u hu hd
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
    have hs : _root_.hammingDist (X.g.sign v.1) (X.g.sign a.1) ≤ R :=
      (X.St.sign_distance v.1 a.1).trans hd
    have hadj := neighbor_sign_bound X y a ha (X.g.sign y.1) 0 (by simp)
    have htriangle := _root_.hammingDist_triangle (X.g.sign v.1) (X.g.sign a.1) (X.g.sign y.1)
    have hnear : _root_.hammingDist (X.g.sign v.1) (X.g.sign y.1) ≤ R + 1 := by omega
    change eligOf X ht H (pos ω) (arraysOf ω) (X.siteOf v) =
      eligOf X ht H' (pos ω') (arraysOf ω') (X.siteOf v)
    rw [hp']
    exact j12_eligOf_congr X ht H H' (pos ω') _ _ v hnear (by omega) hb hc hA

private theorem j12_heavyCount_congr (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H H' : X.KeyHist) (ω ω' : X.CΩ ht) (v : EvenRole5 n)
    (l : ht.hp.Loc) (hb : H.1 = H'.1)
    (hc : ∀ ℓ ∈ (X.g.evenType (X.p.J n) v.1).2.1, H.2 ℓ = H'.2 ℓ)
    (ho : ∀ ℓ ∈ (X.g.optionalKey (X.p.J n) v.1).toFinset, H.2 ℓ = H'.2 ℓ)
    (ha : arraysOf ω (l, X.g.evenType (X.p.J n) v.1) =
      arraysOf ω' (l, X.g.evenType (X.p.J n) v.1)) :
    X.refSubset H ω v l = X.refSubset H' ω' v l ∧
      X.heavyCount H ω v (l, X.refSubset H ω v l) =
        X.heavyCount H' ω' v (l, X.refSubset H' ω' v l) := by
  have hsub := refSubset_ext X H H' (arraysOf ω) (arraysOf ω')
    (l, X.g.evenType (X.p.J n) v.1) (X.g.optionalKey (X.p.J n) v.1) ha ho
  refine ⟨hsub, ?_⟩
  have hlaw : X.blockLaw H (X.g.evenType (X.p.J n) v.1) =
      X.blockLaw H' (X.g.evenType (X.p.J n) v.1) :=
    blockLawOn_ext X H H' (X.g.evenType (X.p.J n) v.1) _ hb hc
  have havg (x) : X.avgMarg H (X.g.evenType (X.p.J n) v.1) x =
      X.avgMarg H' (X.g.evenType (X.p.J n) v.1) x := by simp only [avgMarg, hlaw]
  change heavyCountOn X ht H (arraysOf ω) v _ = heavyCountOn X ht H' (arraysOf ω') v _
  simp only [heavyCountOn, refSubset, hsub, ha, PriorHeavy, havg]
  try rfl

private theorem j12_event_congr (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H H' : X.KeyHist) (ω ω' : X.CΩ ht)
    (y : OddRole5 n) (R q : ℕ) (r : X.RecordOn ht.hp.Loc) (A : X.ArraysOn ht.hp.Loc)
    (hq : R + 4 ≤ q) (hb : H.1 = H'.1)
    (hc : ∀ ℓ, within X (X.g.sign y.1) q ℓ → H.2 ℓ = H'.2 ℓ)
    (hpos : pos ω = pos ω') (hact : act ω = act ω') (htie : tie ω = tie ω')
    (hA : ∀ c, c.2 ∈ localTypes X (X.g.sign y.1) q → arraysOf ω c = arraysOf ω' c) :
    (X.LocalValidAt ht (markElig X ht) H ω R y ∧
      X.actualRecordAt (markElig X ht H) H ω R y = r ∧ ∀ c ∈ r.2.1, arraysOf ω c = A c) =
    (X.LocalValidAt ht (markElig X ht) H' ω' R y ∧
      X.actualRecordAt (markElig X ht H') H' ω' R y = r ∧ ∀ c ∈ r.2.1, arraysOf ω' c = A c) := by
  let σ := fun a => X.selAt (markElig X ht H) ω R a
  let σ' := fun a => X.selAt (markElig X ht H') ω' R a
  let r₀ := recordOf X ht H (arraysOf ω) σ y
  let r₁ := recordOf X ht H' (arraysOf ω') σ' y
  have hσ : ∀ a ∈ evenNbrs y, σ a = σ' a :=
    j12_selections_congr X ht H H' ω ω' y R q hq hb hc hpos hact htie hA
  have hnear (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
      _root_.hammingDist (X.g.sign a.1) (X.g.sign y.1) ≤ 1 :=
    neighbor_sign_bound X y a ha _ 0 (by simp)
  have htypes (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
      ∀ ℓ ∈ (X.g.evenType (X.p.J n) a.1).2.1, within X (X.g.sign y.1) q ℓ :=
    fun ℓ hℓ => within_mono X (by omega) (type_keys_within X a.1 _ 1 (hnear a ha) ℓ hℓ)
  have hopts (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
      ∀ ℓ ∈ (X.g.optionalKey (X.p.J n) a.1).toFinset, within X (X.g.sign y.1) q ℓ :=
    fun ℓ hℓ => within_mono X (by omega) (optional_key_within X a.1 _ 1 (hnear a ha) ℓ hℓ)
  have htarg : within X (X.g.sign y.1) q (X.g.roleKey (X.p.J n) y.1) :=
    role_key_within X y.1 _ q (by simp)
  have hty (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
      X.g.evenType (X.p.J n) a.1 ∈ localTypes X (X.g.sign y.1) q := by
    simp only [localTypes, Finset.mem_filter, Finset.mem_univ, true_and]
    exact htypes a ha
  have harole (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (l) :
      arraysOf ω (l, X.g.evenType (X.p.J n) a.1) =
      arraysOf ω' (l, X.g.evenType (X.p.J n) a.1) := hA _ (hty a ha)
  have hr : r₀ = r₁ := j12_recordOf_congr X ht H H' _ _ σ σ' y hσ harole (hc _ htarg)
  have hd := j12_recordOf_data X ht H (arraysOf ω) σ y htarg htypes hopts
  have harr : ∀ c ∈ recordArrays X r₀, arraysOf ω c = arraysOf ω' c := by
    intro c hc'
    obtain ⟨a, ha, he⟩ := hd.2 c hc'
    exact hA c (he.symm ▸ hty a ha)
  have htests := record_tests_ext X H H' r₀ (arraysOf ω) (arraysOf ω') hb
    (fun ℓ hℓ => hc ℓ (hd.1 ℓ hℓ)) harr
  have hchoose : (∀ a ∈ evenNbrs y, (σ a).isSome) = (∀ a ∈ evenNbrs y, (σ' a).isSome) := by
    apply propext
    exact forall_congr' fun a => imp_congr_right (fun ha => by rw [hσ a ha])
  have hcard : ((evenNbrs y).image σ).card = ((evenNbrs y).image σ').card := by
    congr 1
    exact Finset.image_congr hσ
  have hhit (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (l k)
      (hk : X.g.optionalKey (X.p.J n) a.1 = some (.inl k)) :
      X.hitSet (arraysOf ω) (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k) =
      X.hitSet (arraysOf ω') (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H'.2 k) := by
    have he := hc (.inl k) (hopts a ha _ (by simp [hk]))
    simp only [Setup5.hitSet, harole a ha l, Setup5.lowCol, he]
    try rfl
  have hhits :
      (∀ a ∈ evenNbrs y, ∀ l k, σ a = some l → X.g.optionalKey (X.p.J n) a.1 = some (.inl k) →
        X.p.usedBlocks n ≤
          (X.hitSet (arraysOf ω) (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k)).card) =
      (∀ a ∈ evenNbrs y, ∀ l k, σ' a = some l → X.g.optionalKey (X.p.J n) a.1 = some (.inl k) →
        X.p.usedBlocks n ≤
          (X.hitSet (arraysOf ω') (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H'.2 k)).card) := by
    apply propext
    exact forall_congr' fun a => imp_congr_right fun ha => forall_congr' fun l =>
      forall_congr' fun k => by
        rw [hσ a ha]
        exact imp_congr_right fun _ => imp_congr_right fun hk => by rw [hhit a ha l k hk]
  have hheavy (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (l) :=
    j12_heavyCount_congr X ht H H' ω ω' a l hb
      (fun ℓ hℓ => hc ℓ (htypes a ha ℓ hℓ)) (fun ℓ hℓ => hc ℓ (hopts a ha ℓ hℓ)) (harole a ha l)
  have hheavies :
      (∀ a ∈ evenNbrs y, ∀ l, σ a = some l →
        (X.heavyCount H ω a (l, X.refSubset H ω a l) : ℝ) ≤
          X.p.nu0 * (X.refLen (X.g.evenType (X.p.J n) a.1) (X.refSubset H ω a l) : ℝ)) =
      (∀ a ∈ evenNbrs y, ∀ l, σ' a = some l →
        (X.heavyCount H' ω' a (l, X.refSubset H' ω' a l) : ℝ) ≤
          X.p.nu0 * (X.refLen (X.g.evenType (X.p.J n) a.1) (X.refSubset H' ω' a l) : ℝ)) := by
    apply propext
    exact forall_congr' fun a => imp_congr_right fun ha => forall_congr' fun l => by
      rw [hσ a ha, (hheavy a ha l).2, (hheavy a ha l).1]
  have hobsarr : ∀ c ∈ r₀.2.1, arraysOf ω c = arraysOf ω' c := by
    intro c hc'
    apply harr c
    simp only [recordArrays, Finset.mem_union]
    exact Or.inl (Or.inl hc')
  have hraw : (∀ c ∈ r₀.2.1, ∀ i, X.blockWeight H c.2 c.2.2.1 (arraysOf ω c i) ≠ 0) =
      (∀ c ∈ r₀.2.1, ∀ i, X.blockWeight H' c.2 c.2.2.1 (arraysOf ω' c i) ≠ 0) := by
    apply propext
    apply forall_congr'
    intro c
    apply imp_congr_right
    intro hco
    apply forall_congr'
    intro i
    have hk : ∀ ℓ ∈ c.2.2.1, H.2 ℓ = H'.2 ℓ := by
      intro ℓ hℓ
      apply hc
      obtain ⟨a, ha, he⟩ := j12_recordOf_obs_type X ht H (arraysOf ω) σ y c hco
      exact htypes a ha ℓ (he ▸ hℓ)
    have hw : X.blockWeight H c.2 c.2.2.1 (arraysOf ω c i) =
        X.blockWeight H' c.2 c.2.2.1 (arraysOf ω' c i) := by
      unfold Setup5.blockWeight
      rw [hb, hobsarr c hco]
      congr 1
      exact Finset.prod_congr rfl (fun ℓ hℓ => by rw [hk ℓ hℓ])
    rw [hw]
  have hvalid : X.LocalValidAt ht (markElig X ht) H ω R y =
      X.LocalValidAt ht (markElig X ht) H' ω' R y := by
    change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) = _
    change (X.baseLaw.w H.1 ≠ 0 ∧ X.Step1Pass H.1 ∧
      (∀ a ∈ evenNbrs y, (σ a).isSome) ∧ _ ∧ ((evenNbrs y).image σ).card ≤ X.p.T n ∧
      _ ∧ _ ∧ (∀ c ∈ r₀.2.1, ∀ i, X.blockWeight H c.2 c.2.2.1 (arraysOf ω c i) ≠ 0) ∧
      0 < X.step3PostOn H r₀ (arraysOf ω) none (H.2 (X.g.roleKey (X.p.J n) y.1)) ∧
      X.candGateOn H r₀ (arraysOf ω) (H.2 (X.g.roleKey (X.p.J n) y.1)) ∧
      ¬ X.step3FailOn H r₀ (arraysOf ω)) = _
    rw [hb, hchoose, hpos, hcard, hhits, hheavies, hraw, htests.1,
      htests.2.1 none (H.2 (X.g.roleKey (X.p.J n) y.1)),
      htests.2.2 (H.2 (X.g.roleKey (X.p.J n) y.1)), hc _ htarg]
    let tail (d : Finset (ht.hp.Loc × X.Ty) ×
        Finset (ht.hp.Loc × X.Ty × Option X.Key) ×
        Option (ht.hp.Loc × X.Ty × Finset (Fin X.blockBound))) : Prop :=
      (∀ c ∈ d.1, ∀ i, X.blockWeight H' c.2 c.2.2.1 (arraysOf ω' c i) ≠ 0) ∧
      0 < X.step3PostOn H' (X.g.roleKey (X.p.J n) y.1, d) (arraysOf ω') none
        (H'.2 (X.g.roleKey (X.p.J n) y.1)) ∧
      X.candGateOn H' (X.g.roleKey (X.p.J n) y.1, d) (arraysOf ω')
        (H'.2 (X.g.roleKey (X.p.J n) y.1)) ∧
      ¬ X.step3FailOn H' (X.g.roleKey (X.p.J n) y.1, d) (arraysOf ω')
    have htail : tail r₀.2 = tail r₁.2 := congrArg tail (congrArg Prod.snd hr)
    change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ tail r₀.2) =
      (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ tail r₁.2)
    rw [htail]
  change (X.LocalValidAt ht (markElig X ht) H ω R y ∧ r₀ = r ∧ _) =
    (X.LocalValidAt ht (markElig X ht) H' ω' R y ∧ r₁ = r ∧ _)
  rw [hvalid, ← hr]
  apply propext
  apply and_congr_right
  intro _
  apply and_congr_right
  intro he
  subst r
  exact forall_congr' fun c => imp_congr_right (fun hco => by rw [hobsarr c hco])

private theorem j12_mass_congr (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (H H' : X.KeyHist) (y : OddRole5 n)
    (r : X.RecordOn ht.hp.Loc) (A : X.ArraysOn ht.hp.Loc)
    (q : ℕ) (hq : ht.hp.Rshort (X.p.m n) + 4 ≤ q)
    (hb : H.1 = H'.1) (hc : ∀ ℓ, within X (X.g.sign y.1) q ℓ → H.2 ℓ = H'.2 ℓ) :
    shortPresMassOf X ht (markElig X ht) H y r A = shortPresMassOf X ht (markElig X ht) H' y r A := by
  let U := localTypes X (X.g.sign y.1) q
  let F := fun (H : X.KeyHist) (ω : X.CΩ ht) =>
    X.LocalValidAt ht (markElig X ht) H ω (ht.hp.Rshort (X.p.m n)) y ∧
    X.actualRecordAt (markElig X ht H) H ω (ht.hp.Rshort (X.p.m n)) y = r ∧
    ∀ c ∈ r.2.1, arraysOf ω c = A c
  have hm (H : X.KeyHist) (ω : X.CΩ ht) : F H ω = F H (j12_maskΩ X ht U ω) := by
    apply j12_event_congr X ht H H ω (j12_maskΩ X ht U ω) y _ q r A hq rfl (fun _ _ => rfl)
    · rfl
    · rfl
    · rfl
    · intro c hc
      show arraysOf ω c = maskArrays X U (ω c.1).2.2.2 c.2
      unfold maskArrays
      rw [if_pos hc]
      rfl
  have hF : F H = F H' := by
    funext ω
    exact j12_event_congr X ht H H' ω ω y _ q r A hq hb hc rfl rfl rfl (fun _ _ => rfl)
  change (X.centreLaw ht H).pr (F H) = (X.centreLaw ht H').pr (F H')
  calc
    (X.centreLaw ht H).pr (F H) = (FinProb.map (X.centreLaw ht H) (j12_maskΩ X ht U)).pr (F H) := by
      rw [pr_map]
      exact congrArg (fun B : X.CΩ ht → Prop => (X.centreLaw ht H).pr B) (funext (hm H))
    _ = (FinProb.map (X.centreLaw ht H') (j12_maskΩ X ht U)).pr (F H') := by
      rw [j12_masked_law X ht H H' _ q hb hc, hF]
    _ = (X.centreLaw ht H').pr (F H') := by
      rw [pr_map]
      exact congrArg (fun B : X.CΩ ht → Prop => (X.centreLaw ht H').pr B)
        (funext fun ω => (hm H' ω).symm)

end J12

/-- SUB-LEMMA J12 (05:991–1001): the short presentation reads low keys only at sign distance
`O(√m)`: the short tube, bounded star distances, `CubeStates5.sign_distance`, and integration of
unread arrays. -/
theorem presentation_local : ∃ Ckey : ℕ, ∀ p : Params5 γ K' χ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ b hi y r a, FinProb.DependsOn
        (fun lo => shortPresMassOf X (canonHt X) (markElig X (canonHt X)) (b, X.joinHidden hi lo) y r a)
        (Finset.univ.filter fun k : X.LowIdx =>
          hammingDist k.2.1 (X.g.sign y.1) ≤ Ckey * Nat.sqrt (X.p.m n)) := by
  refine ⟨16, fun p => ⟨1, ?_⟩⟩
  intro n hn N E G X _ b hi y r a _ _ hlo
  have hm : 1 ≤ X.p.m n := by
    unfold Params5.m
    apply Nat.one_le_ceil_iff.mpr
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  have hs : 1 ≤ Nat.sqrt (X.p.m n) := Nat.succ_le_of_lt (Nat.sqrt_pos.mpr (by omega))
  apply j12_mass_congr X (canonHt X) _ _ y r a (16 * Nat.sqrt (X.p.m n))
  · have hD : (canonHt X).hp.Rshort (X.p.m n) = 8 * Nat.sqrt (X.p.m n) := rfl
    omega
  · rfl
  · intro ℓ hℓ
    cases ℓ with
    | inr i => rfl
    | inl k => exact hlo k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓ⟩)

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

set_option maxHeartbeats 2400000 in
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
  intro cL cH hc Ckey
  have hrecord : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
      (elig : X.KeyHist → X.CΩ ht → ht.hp.EligMap) (H : X.KeyHist) (ω : X.CΩ ht)
      (R : ℕ) (y : OddRole5 n), X.LocalValidAt ht elig H ω R y →
        ∃ μ : X.St.Site → ht.hp.Loc,
          X.RecordFrom (X.actualRecordAt (elig H) H ω R y) y μ ∧
            (Lane_sol_s05_k1.recordIds X (X.actualRecordAt (elig H) H ω R y)).card ≤ X.p.T n := by
    intro n N E G X ht elig H ω R y hv
    rcases hv with ⟨hb, hstep1, hsel, hcounts, hT, hhits, hheavy, hraw, hpath, hgate, hstep3⟩
    let r := X.actualRecordAt (elig H) H ω R y
    let sel := fun a : EvenRole5 n => X.selAt (elig H) ω R a
    let fallback : ht.hp.Loc := (fun _ => false, ⟨0, Nat.zero_lt_succ _⟩)
    let μ : X.St.Site → ht.hp.Loc := fun s =>
      (ht.hp.selectionAt (X.sites ht) (pos ω) (act ω) (elig H ω) (tie ω) R (X.St.oneHot s)).getD fallback
    have hkey : r.1 = X.g.roleKey (X.p.J n) y.1 := rfl
    have hchoose (a : EvenRole5 n) (ha : a ∈ evenNbrs y) : sel a = some (μ (X.St.stateOf a.1)) := by
      change sel a = some ((sel a).getD fallback)
      have hs : (sel a).isSome := hsel a ha
      cases he : sel a with
      | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hs
      | some l => simp only [he, Option.getD_some]
    have ho : r.2.1 = (evenNbrs y).image (fun a => (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1)) := by
      change (evenNbrs y).biUnion (fun a => match sel a with
        | some l => {(l, X.g.evenType (X.p.J n) a.1)} | none => ∅) = _
      ext c
      simp only [Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨a, ha, hc⟩
        have he : c = (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1) := by
          simpa only [hchoose a ha, Finset.mem_singleton] using hc
        exact ⟨a, ha, he.symm⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, by simp only [hchoose a ha, Finset.mem_singleton]⟩
    let pred := fun a : EvenRole5 n =>
      r.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
        r.1.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome
    have href : r.2.2.1 = ((evenNbrs y).filter pred).image
        (fun a => (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)) := by
      change (evenNbrs y).biUnion (fun a => match sel a with
        | some l => if pred a then {(l, X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)} else ∅
        | none => ∅) = _
      ext c
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨a, ha, hc⟩
        by_cases hp : pred a
        · have he : c = (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1,
              X.g.optionalKey (X.p.J n) a.1) := by
            simpa only [hchoose a ha, ite_eq_left hp, Finset.mem_singleton] using hc
          exact ⟨a, ⟨ha, hp⟩, he.symm⟩
        · simp only [hchoose a ha, ite_eq_right hp] at hc
          simp at hc
      · rintro ⟨a, ⟨ha, hp⟩, rfl⟩
        exact ⟨a, ha, by simp only [hchoose a ha, ite_eq_left hp, Finset.mem_singleton]⟩
    have hm : (match r.2.2.2 with
        | none => r.1.isLeft → ∀ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2.isSome
        | some (l, K, M) => r.1.isLeft ∧ ∃ a ∈ evenNbrs y,
          K = X.g.evenType (X.p.J n) a.1 ∧ K.2.2 = none ∧
            l = μ (X.St.stateOf a.1) ∧ X.LegitRef K M) := by
      by_cases hy : X.g.severity y.1 ≤ X.p.J n
      · let k : X.LowIdx := (X.g.key y.1, X.g.sign y.1, ⟨X.g.severity y.1, Nat.lt_succ_of_le hy⟩)
        have hrole : X.g.roleKey (X.p.J n) y.1 = .inl k := by
          simp only [ChunkGeometry5.roleKey, dite_eq_left hy, k]
        have hl : r.1.isLeft := by simp only [hkey, hrole, Sum.isLeft_inl]
        by_cases hex : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (sel a).isSome
        · let a := Classical.choose hex
          have ha := Classical.choose_spec hex
          let l := μ (X.St.stateOf a.1)
          let K := X.g.evenType (X.p.J n) a.1
          let M := X.firstK (X.hitSet (arraysOf ω) (l, K) (X.lowCol H.2 k)) (X.p.usedBlocks n)
          have he : r.2.2.2 = some (l, K, M) := by
            simp only [r, actualRecordAt, hrole]
            rw [dite_eq_left hex]
            change (match sel a with
              | some l' => some (l', K, X.firstK (X.hitSet (arraysOf ω) (l', K) (X.lowCol H.2 k))
                  (X.p.usedBlocks n)) | none => none) = _
            rw [hchoose a ha.1]
          rw [he]
          exact ⟨hl, a, ha.1, rfl, ha.2.1, rfl,
            Lane_sol_s05_k1.mask_legit_of_gate X H r (arraysOf ω) hl hgate (l, K) M he ha.2.1⟩
        · have he : r.2.2.2 = none := by
            simp only [r, actualRecordAt, hrole]
            rw [dite_eq_right hex]
          rw [he]
          intro _ a ha
          cases hK : (X.g.evenType (X.p.J n) a.1).2.2 with
          | none => exact (hex ⟨a, ha, hK, hsel a ha⟩).elim
          | some j => simp only [hK, Option.isSome_some]
      · have he : r.2.2.2 = none := by
          simp only [r, actualRecordAt, ChunkGeometry5.roleKey, dite_eq_right hy]
        rw [he]
        have hl : ¬ r.1.isLeft := by
          simp only [hkey, ChunkGeometry5.roleKey, dite_eq_right hy, Sum.isLeft_inr, Bool.false_eq_true, not_false_eq_true]
        exact fun h => (hl h).elim
    have hids : Lane_sol_s05_k1.recordIds X r = (evenNbrs y).image (fun a => μ (X.St.stateOf a.1)) := by
      simp only [Lane_sol_s05_k1.recordIds, ho, Finset.image_image]
      ext l
      simp only [Finset.mem_image, Function.comp_apply]
    have hchoices : ((evenNbrs y).image (fun a => μ (X.St.stateOf a.1))).image some =
        (evenNbrs y).image sel := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro a ha
      exact (hchoose a ha).symm
    have hsome : Function.Injective (some : ht.hp.Loc → Option ht.hp.Loc) := by
      intro a b h
      exact Option.some.inj h
    refine ⟨μ, ?_, ?_⟩
    · change X.RecordFrom r y μ
      refine ⟨hkey.symm, ?_, ?_, ?_⟩
      · rw [ho]
        ext c
        simp only [Finset.mem_image]
      · rw [href]
        ext c
        simp only [Finset.mem_image, Finset.mem_filter, pred, r, actualRecordAt]
      · cases he : r.2.2.2 with
        | none =>
          simp only [he] at hm ⊢
          exact hm
        | some c =>
          rcases c with ⟨l, K, M⟩
          simp only [he] at hm ⊢
          obtain ⟨hl, a, ha, hK, hhigh, hi, hlegit⟩ := hm
          exact ⟨hl, a, ha, hK, hhigh, hi, hlegit⟩
    · rw [hids, ← Finset.card_image_of_injective _ hsome, hchoices]
      exact hT
  have hselected : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (H : X.KeyHist)
      (ω : X.CΩ L.ht) (R : ℕ) (a : EvenRole5 n) (l : L.ht.hp.Loc),
      X.selAt (L.elig H) ω R a = some l →
        pos ω l = true ∧ _root_.hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.r := by
    intro n N E G X L H ω R a l hs
    obtain ⟨j, hj⟩ := Lane_sol_s05_k1.selectionAt_mem L.ht.hp (X.sites L.ht)
      (pos ω) (act ω) (L.elig H ω) (X.siteOf a) R (tie ω) l hs
    obtain ⟨hP, hlev, hd⟩ := L.elig_shape H ω (X.siteOf a) j l hj
    have he : _root_.hammingDist l.1 (X.siteOf a) = HypercubeRamsey.hammingDist l.1 (X.siteOf a) := by
      unfold _root_.hammingDist HypercubeRamsey.hammingDist
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter]
    exact ⟨hP, he.symm ▸ hd⟩
  have hpool : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (H : X.KeyHist)
      (ω : X.CΩ L.ht) (R : ℕ) (y : OddRole5 n),
      Lane_sol_s05_k1.recordIds X (X.actualRecordAt (L.elig H) H ω R y) ⊆
        (evenNbrs y).biUnion (fun a => Finset.univ.filter (fun l : L.ht.hp.Loc =>
          pos ω l = true ∧ _root_.hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.r)) := by
    intro n N E G X L H ω R y l hl
    obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hl
    subst l
    simp only [actualRecordAt, Finset.mem_biUnion] at hc
    obtain ⟨a, ha, hc⟩ := hc
    cases hs : X.selAt (L.elig H) ω R a with
    | none => simp only [hs] at hc; simp at hc
    | some l =>
      have he : c = (l, X.g.evenType (X.p.J n) a.1) := by
        simpa only [hs, Finset.mem_singleton] using hc
      have hd := hselected n N E G X L H ω R a l hs
      apply Finset.mem_biUnion.mpr
      refine ⟨a, ha, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      simpa only [he] using hd
  have hcover : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (H : X.KeyHist)
      (ω : X.CΩ L.ht) (R : ℕ) (y : OddRole5 n), X.LocalValidAt L.ht L.elig H ω R y →
      X.actualRecordAt (L.elig H) H ω R y ∈ Lane_sol_s05_k1.potentialRecords X y
        ((evenNbrs y).biUnion (fun a => Finset.univ.filter (fun l : L.ht.hp.Loc =>
          pos ω l = true ∧ _root_.hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.r))) := by
    intro n N E G X L H ω R y hv
    obtain ⟨μ, hr, hT⟩ := hrecord n N E G X L.ht L.elig H ω R y hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨μ, hr⟩,
      hpool n N E G X L H ω R y, hT⟩
  have hpool_count : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (H : X.KeyHist)
      (ω : X.CΩ L.ht) (R : ℕ) (y : OddRole5 n), X.LocalValidAt L.ht L.elig H ω R y →
      (((evenNbrs y).biUnion (fun a => Finset.univ.filter (fun l : L.ht.hp.Loc =>
        pos ω l = true ∧ _root_.hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.r))).card : ℝ) ≤
          (n : ℝ) * (L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam) := by
    intro n N E G X L H ω R y hv
    have hdist (u v : CubeVertex L.ht.hp.d) :
        HypercubeRamsey.hammingDist u v = _root_.hammingDist u v := by
      unfold HypercubeRamsey.hammingDist _root_.hammingDist
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter]
    have hcount (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (j : Fin (L.ht.hp.H + 1)) :
        ((Finset.univ.filter (fun u : CubeVertex L.ht.hp.d =>
          pos ω (u, j) = true ∧ _root_.hammingDist u (X.siteOf a) ≤ L.ht.hp.r)).card : ℝ) ≤ 2 * L.ht.hp.lam := by
      have h := hv.2.2.2.1 a ha j
      convert h using 1
      congr 1
    let S := fun a : EvenRole5 n => Finset.univ.filter (fun l : L.ht.hp.Loc =>
      pos ω l = true ∧ _root_.hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.r)
    have hS (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
        ((S a).card : ℝ) ≤ (L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam) :=
      Lane_sol_s05_k1.location_pool_card_le L.ht.hp (pos ω) (X.siteOf a) _ (hcount a ha)
    have hlam : 0 ≤ L.ht.hp.lam := by
      change (0 : ℝ) ≤ (n : ℝ) ^ (10 : ℝ)
      positivity
    calc
      _ ≤ ((∑ a ∈ evenNbrs y, (S a).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ = ∑ a ∈ evenNbrs y, ((S a).card : ℝ) := Nat.cast_sum _ _
      _ ≤ ∑ _a ∈ evenNbrs y, (L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam) :=
        Finset.sum_le_sum hS
      _ = ((evenNbrs y).card : ℝ) * ((L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam)) := by simp
      _ ≤ (n : ℝ) * ((L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam)) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Lane_sol_s05_hist1b.evenNbrs_card_le y)) (by positivity)
      _ = _ := by ring
  have hlookup : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5) (H : X.KeyHist)
      (r : X.RecordOn ht.hp.Loc) (a : X.ArraysOn ht.hp.Loc)
      (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) (F : (ht.hp.Loc → Bool) → Prop),
      (X.centreLaw ht (X.withCol H r.1 θ)).pr (fun ω =>
        F (pos ω) ∧ X.candGateOn H r a θ ∧ ∀ c ∈ r.2.1, arraysOf ω c = a c) =
          ((FinProb.pi fun _ : ht.hp.Loc => FinProb.bernoulli (ht.hp.lam / (ht.hp.V : ℝ))).pr F *
            Lane_sol_s05_k1.observationReferenceMass X H r a) *
              ((if X.candGateOn H r a θ then 1 else 0) * X.obsLikOn H r a θ none) := by
    intro n N E G X ht H r a θ F
    by_cases hg : X.candGateOn H r a θ
    · simp only [hg, true_and, ite_true, one_mul]
      have hraw := Lane_sol_s05_k1.raw_observation_pr
        (fun _ : ht.hp.Loc => FinProb.bernoulli (ht.hp.lam / (ht.hp.V : ℝ)))
        (fun _ : ht.hp.Loc => FinProb.bernoulli ((n : ℝ) ^ ht.b₀ / ht.hp.lam))
        (fun _ : ht.hp.Loc => FinProb.uniformAll (Ω := ht.hp.TiePerm) ⟨1⟩)
        (fun _l (K : X.Ty) => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) =>
          X.blockLaw (X.withCol H r.1 θ) K) F r.2.1 a
      change (X.centreLaw ht (X.withCol H r.1 θ)).pr
        (fun ω => F (pos ω) ∧ ∀ c ∈ r.2.1, arraysOf ω c = a c) = _ at hraw
      rw [hraw, Lane_sol_s05_k1.observation_law_recompose X H r a θ hg]
      ring
    · simp only [hg, false_and, and_false, ite_false, zero_mul, mul_zero]
      simp [FinProb.pr]
  let table : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (C : ℝ),
      X.RecordCount C → 0 < X.p.T n → X.KeyHist → OddRole5 n →
        Lane_sol_s05_k1.PresentationTable (Target := Fin N)
          (Data := Lane_sol_s05_k1.ObservationDatum X (Id := L.ht.hp.Loc)) (Ω := X.CΩ L.ht) := by
    intro n N E G X L C hcount hT H y
    let ℓ := X.g.roleKey (X.p.J n) y.1
    let Hcand := fun x : Fin N => X.withCol H ℓ (fun _ => x)
    let raw := fun x : Fin N => X.centreLaw L.ht (Hcand x)
    let record := fun x ω => X.actualRecordAt (L.elig (Hcand x)) (Hcand x) ω
      (L.ht.hp.Rshort (X.p.m n)) y
    let valid := fun x ω => X.g.low (X.p.J n) y.1 ∧
      X.LocalValidAt L.ht L.elig (Hcand x) ω (L.ht.hp.Rshort (X.p.m n)) y
    let pool := fun ω : X.CΩ L.ht => Lane_sol_s05_k1.neighborPool X.siteOf y L.ht.hp.r (pos ω)
    let B : ℝ := (n : ℝ) * (L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam)
    let records := fun (_x : Fin N) ω => Lane_sol_s05_k1.prospectiveRecords X y (pool ω) B
    let gate := fun (x : Fin N) (ω : X.CΩ L.ht) (r : X.RecordOn L.ht.hp.Loc) =>
      X.candGateOn H r (Lane_sol_s05_k1.observationArrays X
        (Lane_sol_s05_k1.observationDatum X r (arraysOf ω))) (fun _ => x)
    have hrec (x : Fin N) (ω : X.CΩ L.ht) (hv : valid x ω) : record x ω ∈ records x ω := by
      have hsize : ((pool ω).card : ℝ) ≤ B := hpool_count n N E G X L (Hcand x) ω _ y hv.2
      change record x ω ∈ Lane_sol_s05_k1.prospectiveRecords X y (pool ω) B
      rw [Lane_sol_s05_k1.prospectiveRecords, if_pos ⟨hv.1, hsize⟩]
      exact hcover n N E G X L (Hcand x) ω _ y hv.2
    have hgate (x : Fin N) (ω : X.CΩ L.ht) (hv : valid x ω) : gate x ω (record x ω) := by
      let r := record x ω
      have hk : r.1 = ℓ := rfl
      have he : Hcand x = X.withCol H r.1 (fun _ => x) := by rw [hk]
      have hc : (Hcand x).2 r.1 = (fun _ => x) := by
        rw [he]
        exact Function.update_self _ _ _
      have hg : X.candGateOn H r (arraysOf ω) (fun _ => x) := by
        have hg := hv.2.2.2.2.2.2.2.2.2.2.1
        change X.candGateOn (Hcand x) r (arraysOf ω) ((Hcand x).2 r.1) at hg
        rw [hc, he] at hg
        exact (Lane_sol_s05_hist1b.candGateOn_withCol X H r (arraysOf ω) (fun _ => x) (fun _ => x)).mp hg
      obtain ⟨μ, hr, _⟩ := hrecord n N E G X L.ht L.elig (Hcand x) ω _ y hv.2
      change X.candGateOn H r (Lane_sol_s05_k1.observationArrays X
        (Lane_sol_s05_k1.observationDatum X r (arraysOf ω))) (fun _ => x)
      apply (Lane_sol_s05_hist1b.candGateOn_arrays_congr X H r (arraysOf ω)
        (Lane_sol_s05_k1.observationArrays X (Lane_sol_s05_k1.observationDatum X r (arraysOf ω)))
        (Lane_sol_s05_hist1b.record_mask_mem X r y μ hr)
        (fun c hc => (Lane_sol_s05_k1.observationArrays_eq X r (arraysOf ω) c hc).symm)
        (fun _ => x)).mp hg
    have hB : 0 ≤ B := by
      dsimp [B]
      have hLam : 0 ≤ L.ht.hp.lam := by
        change (0 : ℝ) ≤ (n : ℝ) ^ (10 : ℝ)
        positivity
      positivity
    exact Lane_sol_s05_k1.observationTable X record (fun _ ω => arraysOf ω) valid
      (X.prior H.1 ℓ) raw records gate (Lane_sol_s05_k1.lookupBudget X C B y) hrec hgate
      (fun x ω => Lane_sol_s05_k1.prospectiveRecords_card_le X C B y (pool ω)
        (fun _ => false, ⟨0, Nat.zero_lt_succ _⟩) hB hT hcount)
  have htable_lik : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (C : ℝ)
      (hcount : X.RecordCount C) (hT : 0 < X.p.T n) (H : X.KeyHist) (y : OddRole5 n)
      (d : Lane_sol_s05_k1.ObservationDatum X (Id := L.ht.hp.Loc)),
      d.1.1 = X.g.roleKey (X.p.J n) y.1 → ∀ x : Fin N,
      (table n N E G X L C hcount hT H y).likelihood x d =
        (((FinProb.pi fun _ : L.ht.hp.Loc => FinProb.bernoulli (L.ht.hp.lam / (L.ht.hp.V : ℝ))).pr
          (fun P => d.1 ∈ Lane_sol_s05_k1.prospectiveRecords X y
            (Lane_sol_s05_k1.neighborPool X.siteOf y L.ht.hp.r P)
              ((n : ℝ) * (L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam)))) *
            Lane_sol_s05_k1.observationReferenceMass X H d.1 (Lane_sol_s05_k1.observationArrays X d)) *
              ((if X.candGateOn H d.1 (Lane_sol_s05_k1.observationArrays X d) (fun _ => x) then 1 else 0) *
                X.obsLikOn H d.1 (Lane_sol_s05_k1.observationArrays X d) (fun _ => x) none) := by
    intro n N E G X L C hcount hT H y d hk x
    let B : ℝ := (n : ℝ) * (L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam)
    let F := fun P : L.ht.hp.Loc → Bool => d.1 ∈ Lane_sol_s05_k1.prospectiveRecords X y
      (Lane_sol_s05_k1.neighborPool X.siteOf y L.ht.hp.r P) B
    let gateD := fun d' : Lane_sol_s05_k1.ObservationDatum X (Id := L.ht.hp.Loc) =>
      X.candGateOn H d'.1 (Lane_sol_s05_k1.observationArrays X d') (fun _ => x)
    change (X.centreLaw L.ht (X.withCol H (X.g.roleKey (X.p.J n) y.1) (fun _ => x))).pr
      (fun ω => d ∈ Lane_sol_s05_k1.observationCover X
        (Lane_sol_s05_k1.prospectiveRecords X y
          (Lane_sol_s05_k1.neighborPool X.siteOf y L.ht.hp.r (pos ω)) B)
        (arraysOf ω) (fun r => gateD (Lane_sol_s05_k1.observationDatum X r (arraysOf ω)))) = _
    rw [← hk]
    have he : (fun ω : X.CΩ L.ht => d ∈ Lane_sol_s05_k1.observationCover X
        (Lane_sol_s05_k1.prospectiveRecords X y
          (Lane_sol_s05_k1.neighborPool X.siteOf y L.ht.hp.r (pos ω)) B)
        (arraysOf ω) (fun r => gateD (Lane_sol_s05_k1.observationDatum X r (arraysOf ω)))) =
      (fun ω => F (pos ω) ∧ X.candGateOn H d.1 (Lane_sol_s05_k1.observationArrays X d) (fun _ => x) ∧
        ∀ c ∈ d.1.2.1, arraysOf ω c = Lane_sol_s05_k1.observationArrays X d c) := by
      funext ω
      exact propext (Lane_sol_s05_k1.observationCover_mem_iff X _ (arraysOf ω) gateD d)
    rw [he]
    exact hlookup n N E G X L.ht H d.1 (Lane_sol_s05_k1.observationArrays X d) (fun _ => x) F
  have htable_lik_nekey : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (C : ℝ)
      (hcount : X.RecordCount C) (hT : 0 < X.p.T n) (H : X.KeyHist) (y : OddRole5 n)
      (d : Lane_sol_s05_k1.ObservationDatum X (Id := L.ht.hp.Loc)),
      d.1.1 ≠ X.g.roleKey (X.p.J n) y.1 → ∀ x : Fin N,
        (table n N E G X L C hcount hT H y).likelihood x d = 0 := by
    intro n N E G X L C hcount hT H y d hk x
    change (X.centreLaw L.ht (X.withCol H (X.g.roleKey (X.p.J n) y.1) (fun _ => x))).pr
      (fun ω => d ∈ Lane_sol_s05_k1.observationCover X
        (Lane_sol_s05_k1.prospectiveRecords X y
          (Lane_sol_s05_k1.neighborPool X.siteOf y L.ht.hp.r (pos ω))
            ((n : ℝ) * (L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam)))
        (arraysOf ω) (fun r => X.candGateOn H r (Lane_sol_s05_k1.observationArrays X
          (Lane_sol_s05_k1.observationDatum X r (arraysOf ω))) (fun _ => x))) = 0
    unfold FinProb.pr
    apply Finset.sum_eq_zero
    intro ω _
    apply if_neg
    intro hd
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hd
    have hrd : r = d.1 := congrArg Sigma.fst he
    exact hk (hrd ▸ Lane_sol_s05_k1.prospectiveRecords_mem_key X y _ _ r (Finset.mem_filter.mp hr).1)
  have htable_post : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (C : ℝ)
      (hcount : X.RecordCount C) (hT : 0 < X.p.T n) (H : X.KeyHist) (y : OddRole5 n)
      (d : Lane_sol_s05_k1.ObservationDatum X (Id := L.ht.hp.Loc)),
      d.1.1 = X.g.roleKey (X.p.J n) y.1 → d.1.1.isLeft →
        (table n N E G X L C hcount hT H y).experiment.baseMass d ≠ 0 → ∀ x : Fin N,
        (table n N E G X L C hcount hT H y).experiment.baseRow d x =
          X.step3PostOn H d.1 (Lane_sol_s05_k1.observationArrays X d) none (fun _ => x) := by
    intro n N E G X L C hcount hT H y d hk hl hm x
    let T := table n N E G X L C hcount hT H y
    let a := Lane_sol_s05_k1.observationArrays X d
    let f := fun x : Fin N =>
      (if X.candGateOn H d.1 a (fun _ => x) then 1 else 0) * X.obsLikOn H d.1 a (fun _ => x) none
    let c := ((FinProb.pi fun _ : L.ht.hp.Loc => FinProb.bernoulli (L.ht.hp.lam / (L.ht.hp.V : ℝ))).pr
      (fun P => d.1 ∈ Lane_sol_s05_k1.prospectiveRecords X y
        (Lane_sol_s05_k1.neighborPool X.siteOf y L.ht.hp.r P)
          ((n : ℝ) * (L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam)))) *
            Lane_sol_s05_k1.observationReferenceMass X H d.1 a
    have hlik : ∀ x, T.likelihood x d = c * f x := htable_lik n N E G X L C hcount hT H y d hk
    have hc : c ≠ 0 := by
      intro hz
      apply hm
      rw [T.experiment_baseMass_factor d c f hlik, hz, zero_mul]
    rw [T.experiment_baseRow_factor d c f hc hlik x]
    have hp : T.prior = X.prior H.1 d.1.1 := by
      change X.prior H.1 (X.g.roleKey (X.p.J n) y.1) = _
      rw [hk]
    rw [hp]
    unfold Setup5.step3PostOn
    simp only [Lane_sol_s05_k1.low_key_length X d.1.1 hl, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, pow_one]
    rw [Lane_sol_s05_k1.low_step3Mass_sum X H d.1 a hl]
    simp only [f, mul_assoc, a]
  have htable_withCol : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (C : ℝ)
      (hcount : X.RecordCount C) (hT : 0 < X.p.T n) (H : X.KeyHist) (y : OddRole5 n) (z : Fin N),
      table n N E G X L C hcount hT
        (X.withCol H (X.g.roleKey (X.p.J n) y.1) (fun _ => z)) y =
          table n N E G X L C hcount hT H y := by
    intro n N E G X L C hcount hT H y z
    let ℓ := X.g.roleKey (X.p.J n) y.1
    let H' := X.withCol H ℓ (fun _ => z)
    let T' := table n N E G X L C hcount hT H' y
    let T := table n N E G X L C hcount hT H y
    change T' = T
    dsimp only [T', T]
    apply Lane_sol_s05_k1.PresentationTable.ext_fields
    · change X.prior H'.1 ℓ = X.prior H.1 ℓ
      simp only [H', Setup5.withCol]
    · funext x
      change X.centreLaw L.ht (X.withCol (X.withCol H ℓ (fun _ => z)) ℓ (fun _ => x)) =
        X.centreLaw L.ht (X.withCol H ℓ (fun _ => x))
      rw [Lane_sol_s05_hist1b.withCol_withCol]
    · change Lane_sol_s05_k1.observationPresentation X
        (fun x ω => X.actualRecordAt (L.elig (X.withCol H' ℓ (fun _ => x)))
          (X.withCol H' ℓ (fun _ => x)) ω (L.ht.hp.Rshort (X.p.m n)) y)
        (fun _ ω => arraysOf ω)
        (fun x ω => X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig
          (X.withCol H' ℓ (fun _ => x)) ω (L.ht.hp.Rshort (X.p.m n)) y) =
        Lane_sol_s05_k1.observationPresentation X
        (fun x ω => X.actualRecordAt (L.elig (X.withCol H ℓ (fun _ => x)))
          (X.withCol H ℓ (fun _ => x)) ω (L.ht.hp.Rshort (X.p.m n)) y)
        (fun _ ω => arraysOf ω)
        (fun x ω => X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig
          (X.withCol H ℓ (fun _ => x)) ω (L.ht.hp.Rshort (X.p.m n)) y)
      simp only [H', Lane_sol_s05_hist1b.withCol_withCol]
    · funext x d
      by_cases hk : d.1.1 = ℓ
      · rw [htable_lik n N E G X L C hcount hT H' y d hk x,
          htable_lik n N E G X L C hcount hT H y d hk x]
        have he : H' = X.withCol H d.1.1 (fun _ => z) := by rw [hk]
        rw [he, Lane_sol_s05_k1.observationReferenceMass_withCol,
          Lane_sol_s05_hist1b.candGateOn_withCol, Lane_sol_s05_hist1b.obsLikOn_withCol]
      · rw [htable_lik_nekey n N E G X L C hcount hT H' y d hk x,
          htable_lik_nekey n N E G X L C hcount hT H y d hk x]
    · change Lane_sol_s05_k1.lookupBudget X C
        ((n : ℝ) * (L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam)) y =
        Lane_sol_s05_k1.lookupBudget X C
        ((n : ℝ) * (L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam)) y
      rfl
  let row : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (C : ℝ),
      X.RecordCount C → 0 < X.p.T n → ℕ → X.KeyHist → X.CΩ L.ht → OddRole5 n → X.OddOut → ℝ := by
    intro n N E G X L C hcount hT R H ω y o
    let T := table n N E G X L C hcount hT H y
    let source := fun d : Lane_sol_s05_k1.ObservationDatum X (Id := L.ht.hp.Loc) =>
      fun x : Fin N => X.step3PostOn H d.1 (Lane_sol_s05_k1.observationArrays X d) none (fun _ => x)
    exact if (o.1 : ℕ) = 0 then
      T.completedRow (Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1)))) source
        (Lane_sol_s05_k1.datumIf X (X.actualRecordAt (L.elig H) H ω R y) (arraysOf ω)
          (X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H ω R y)) o.2 else 0
  have hrow_short : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (C : ℝ)
      (hcount : X.RecordCount C) (hT : 0 < X.p.T n) (H : X.KeyHist) (y : OddRole5 n) (z : Fin N)
      (ω : X.CΩ L.ht) (x : Fin N),
      row n N E G X L C hcount hT (L.ht.hp.Rshort (X.p.m n))
        (X.withCol H (X.g.roleKey (X.p.J n) y.1) (fun _ => z)) ω y (0, x) =
      (table n N E G X L C hcount hT H y).completedRow
        (Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1))))
        (fun d x => X.step3PostOn H d.1 (Lane_sol_s05_k1.observationArrays X d) none (fun _ => x))
        ((table n N E G X L C hcount hT H y).present z ω) x := by
    intro n N E G X L C hcount hT H y z ω x
    let H' := X.withCol H (X.g.roleKey (X.p.J n) y.1) (fun _ => z)
    let R := L.ht.hp.Rshort (X.p.m n)
    let d := Lane_sol_s05_k1.observationDatum X (X.actualRecordAt (L.elig H') H' ω R y) (arraysOf ω)
    let T := table n N E G X L C hcount hT H y
    let ε := Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1)))
    change (table n N E G X L C hcount hT H' y).completedRow ε
        (fun d x => X.step3PostOn H' d.1 (Lane_sol_s05_k1.observationArrays X d) none (fun _ => x))
        (Lane_sol_s05_k1.datumIf X (X.actualRecordAt (L.elig H') H' ω R y) (arraysOf ω)
          (X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H' ω R y)) x =
      T.completedRow ε
        (fun d x => X.step3PostOn H d.1 (Lane_sol_s05_k1.observationArrays X d) none (fun _ => x))
        (Lane_sol_s05_k1.datumIf X (X.actualRecordAt (L.elig H') H' ω R y) (arraysOf ω)
          (X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H' ω R y)) x
    rw [htable_withCol n N E G X L C hcount hT H y z]
    by_cases hv : X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H' ω R y
    · simp only [Lane_sol_s05_k1.datumIf, hv, ite_true]
      change T.completedProxy ε
        (fun d x => X.step3PostOn H' d.1 (Lane_sol_s05_k1.observationArrays X d) none (fun _ => x)) d x =
        T.completedProxy ε
        (fun d x => X.step3PostOn H d.1 (Lane_sol_s05_k1.observationArrays X d) none (fun _ => x)) d x
      apply T.completedProxy_source_congr
      exact Lane_sol_s05_k1.low_step3Post_withCol X H d.1 (Lane_sol_s05_k1.observationArrays X d) (fun _ => z) x
    · simp only [Lane_sol_s05_k1.datumIf, hv, ite_false, Lane_sol_s05_k1.PresentationTable.completedRow]
  have hrow_mean : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (C : ℝ)
      (hcount : X.RecordCount C) (hT : 0 < X.p.T n) (H : X.KeyHist) (y : OddRole5 n) (x : Fin N),
      ∑ z, (X.prior H.1 (X.g.roleKey (X.p.J n) y.1)).w z *
        (X.centreLaw L.ht (X.withCol H (X.g.roleKey (X.p.J n) y.1) (fun _ => z))).expect
          (fun ω => (N : ℝ) * row n N E G X L C hcount hT (L.ht.hp.Rshort (X.p.m n))
            (X.withCol H (X.g.roleKey (X.p.J n) y.1) (fun _ => z)) ω y (0, x)) =
        (N : ℝ) * ∑ d, (table n N E G X L C hcount hT H y).experiment.selectedMass d *
          (table n N E G X L C hcount hT H y).experiment.proxyRow
            (Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1)))) d x := by
    intro n N E G X L C hcount hT H y x
    let T := table n N E G X L C hcount hT H y
    let source := fun d : Lane_sol_s05_k1.ObservationDatum X (Id := L.ht.hp.Loc) =>
      fun x => X.step3PostOn H d.1 (Lane_sol_s05_k1.observationArrays X d) none (fun _ => x)
    let ε := Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1)))
    exact T.short_mean_external ε (N : ℝ) source
      (X.prior H.1 (X.g.roleKey (X.p.J n) y.1))
      (fun z => X.centreLaw L.ht (X.withCol H (X.g.roleKey (X.p.J n) y.1) (fun _ => z)))
      (fun z ω x => row n N E G X L C hcount hT (L.ht.hp.Rshort (X.p.m n))
        (X.withCol H (X.g.roleKey (X.p.J n) y.1) (fun _ => z)) ω y (0, x))
      rfl (fun _ => rfl) (hrow_short n N E G X L C hcount hT H y) x
  have hrow_nonneg : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (C : ℝ)
      (hcount : X.RecordCount C) (hT : 0 < X.p.T n) (R : ℕ) (H : X.KeyHist) (ω : X.CΩ L.ht)
      (y : OddRole5 n) (o : X.OddOut), 0 ≤ row n N E G X L C hcount hT R H ω y o := by
    intro n N E G X L C hcount hT R H ω y o
    change 0 ≤ if (o.1 : ℕ) = 0 then _ else 0
    split_ifs
    · apply Lane_sol_s05_k1.PresentationTable.completedRow_nonneg
      intro d x
      exact Lane_sol_s05_centres.step3Post_nonneg X H d.1 (Lane_sol_s05_k1.observationArrays X d) (fun _ => x)
    · exact le_rfl
  have hrow_bound : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (C : ℝ)
      (hcount : X.RecordCount C) (hT : 0 < X.p.T n) (R : ℕ) (H : X.KeyHist) (ω : X.CΩ L.ht)
      (y : OddRole5 n) (o : X.OddOut),
      row n N E G X L C hcount hT R H ω y o ≤
        Real.exp (X.p.delta * X.p.kPrime n (X.g.severity y.1)) *
          X.step3PostOn H (X.actualRecordAt (L.elig H) H ω R y) (arraysOf ω) none (fun _ => o.2) := by
    intro n N E G X L C hcount hT R H ω y o
    let r := X.actualRecordAt (L.elig H) H ω R y
    let d := Lane_sol_s05_k1.observationDatum X r (arraysOf ω)
    let T := table n N E G X L C hcount hT H y
    let source := fun d : Lane_sol_s05_k1.ObservationDatum X (Id := L.ht.hp.Loc) =>
      fun x => X.step3PostOn H d.1 (Lane_sol_s05_k1.observationArrays X d) none (fun _ => x)
    let ε := Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1)))
    change (if (o.1 : ℕ) = 0 then T.completedRow ε source
      (Lane_sol_s05_k1.datumIf X r (arraysOf ω)
        (X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H ω R y)) o.2 else 0) ≤ _
    have hright : 0 ≤ Real.exp (X.p.delta * X.p.kPrime n (X.g.severity y.1)) *
        X.step3PostOn H r (arraysOf ω) none (fun _ => o.2) :=
      mul_nonneg (Real.exp_nonneg _) (Lane_sol_s05_centres.step3Post_nonneg X H r (arraysOf ω) (fun _ => o.2))
    by_cases hi : (o.1 : ℕ) = 0
    · rw [if_pos hi]
      by_cases hv : X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H ω R y
      · have hl : r.1.isLeft := by
          have hy : X.g.severity y.1 ≤ X.p.J n := hv.1
          change (X.g.roleKey (X.p.J n) y.1).isLeft
          simp only [ChunkGeometry5.roleKey, dite_eq_left hy, Sum.isLeft_inl]
        obtain ⟨μ, hr, _⟩ := hrecord n N E G X L.ht L.elig H ω R y hv.2
        have hpost (x : Fin N) : X.step3PostOn H r (arraysOf ω) none (fun _ => x) = source d x :=
          Lane_sol_s05_centres.step3Post_arrays_congr X H r (arraysOf ω)
            (Lane_sol_s05_k1.observationArrays X d) (Lane_sol_s05_hist1b.record_mask_mem X r y μ hr)
            (fun c hc => (Lane_sol_s05_k1.observationArrays_eq X r (arraysOf ω) c hc).symm) none (fun _ => x)
        have hε1 : ε ≤ 1 := Real.exp_le_one_iff.mpr (by
          have hh := mul_nonneg X.p.hdelta.1.le (Nat.cast_nonneg (X.p.kPrime n (X.g.severity y.1)))
          linarith)
        have hbase : T.experiment.baseMass d ≠ 0 → ∀ x, T.experiment.baseRow d x = source d x :=
          htable_post n N E G X L C hcount hT H y d rfl hl
        have hb := T.completedProxy_le_source ε source (Real.exp_pos _) hε1 d
          (fun x => Lane_sol_s05_centres.step3Post_nonneg X H d.1 (Lane_sol_s05_k1.observationArrays X d) (fun _ => x))
          hbase o.2
        simp only [Lane_sol_s05_k1.datumIf, hv, ite_true]
        change T.completedProxy ε source d o.2 ≤ _
        have hInv : ε⁻¹ = Real.exp (X.p.delta * X.p.kPrime n (X.g.severity y.1)) := by
          simp only [ε, Real.exp_neg, inv_inv]
        rw [hInv, ← hpost o.2] at hb
        exact hb
      · simp only [Lane_sol_s05_k1.datumIf, hv, ite_false, Lane_sol_s05_k1.PresentationTable.completedRow]
        exact hright
    · rw [if_neg hi]
      exact hright
  obtain ⟨C, hC, hcount_all⟩ := L5_1e_count (γ := γ) (K' := K') (χ := χ)
  refine ⟨Ckey + 2, Lane_sol_s05_k1.recordRequest C, ?_⟩
  intro p hp
  obtain ⟨nC, hnC⟩ := hcount_all p
  have hlarge := (Lane_sol_s05_k1.record_budget_eventually C hC.le p hp).and
    ((Lane_sol_s05_k1.cap_scales_eventually p).and
    ((Lane_sol_s05_h5l.low_pattern_overhead_eventually p).and
    ((Lane_sol_s05_h5l.fixed_power_margin p (2001 * C / Real.log 2) (51 / 1000) (3 / 50) (by norm_num)).and
    (((Lane_sol_s05_h1.tendsto_m p).eventually_ge_atTop 4).and
    ((Filter.eventually_ge_atTop nC).and (Filter.eventually_ge_atTop (1 : ℕ)))))))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨n₀, ?_⟩
  intro n hn N E G X hXp hcoarse L LL
  obtain ⟨hrecnum, hcapnum, hpattern, hstarMargin, hm4, hnC', hn1⟩ := hn₀ n hn
  have hcount : X.RecordCount C := hnC n hnC' N E G X hXp
  have hT2 : 2 ≤ X.p.T n := by simpa only [hXp] using hcapnum.1
  have hT0 : 0 < X.p.T n := by omega
  have hmX : (4 : ℝ) ≤ X.p.m n := by simpa only [hXp] using hm4
  have hlenX : ∀ j : ℕ, j ≤ X.p.J n + 2 →
      (X.p.q0 * X.p.uSeg n j * X.p.lowBlocks n j : ℕ) ≤ (X.p.m n : ℝ) ^ (3 / 50 : ℝ) ∧
        X.p.Kcap * ((X.p.q0 : ℝ) * X.p.uSeg n j) ≤ (X.p.m n : ℝ) ^ (3 / 50 : ℝ) := by
    simpa only [hXp] using hcapnum.2.2.1
  have hcapX : (1 + 2 * X.p.delta + |X.p.a 2|) * (X.p.m n : ℝ) ^ (61 / 500 : ℝ) ≤ X.p.DL n := by
    simpa only [hXp] using hcapnum.2.2.2
  have hTupper : (X.p.T n : ℝ) ≤ (X.p.m n : ℝ) ^ (1 / 500 : ℝ) := by
    simpa only [hXp] using hcapnum.2.1
  have hpatternX : (X.p.T n : ℝ) * Real.log (X.p.T n) +
      (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) ≤ (X.p.m n : ℝ) ^ (1 / 50 : ℝ) := by
    simpa only [hXp] using hpattern
  have hstarMarginX : (2001 * C / Real.log 2) * (X.p.m n : ℝ) ^ (51 / 1000 : ℝ) ≤
      (X.p.m n : ℝ) ^ (3 / 50 : ℝ) := by simpa only [hXp] using hstarMargin
  have hHn : L.ht.hp.H ≤ n := by
    have hHslack : L.ht.hp.H ≤ L.slack := by
      have h := L.slack_large
      change 2 * 8 * L.ht.hp.H + 32 ≤ L.slack at h
      omega
    have hs : (L.slack : ℝ) ≤ n := by
      calc
        _ ≤ (n : ℝ) ^ (1 - (L.ht.ζ - L.ht.σ) / 4) := L.slack_small
        _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast hn1) (by linarith [L.ht.adm.hsz.2.1])
        _ = _ := Real.rpow_one _
    exact hHslack.trans (Nat.cast_le.mp hs)
  let tab := table n N E G X L C hcount hT0
  let rowAt := row n N E G X L C hcount hT0
  have hsum (R : ℕ) (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n)
      (hv : X.LocalValidAt L.ht L.elig H ω R y) (hy : X.g.low (X.p.J n) y.1) :
      ∑ o, rowAt R H ω y o = 1 := by
    let r := X.actualRecordAt (L.elig H) H ω R y
    let d := Lane_sol_s05_k1.observationDatum X r (arraysOf ω)
    let T := tab H y
    let source := fun d : Lane_sol_s05_k1.ObservationDatum X (Id := L.ht.hp.Loc) =>
      fun x : Fin N => X.step3PostOn H d.1 (Lane_sol_s05_k1.observationArrays X d) none (fun _ => x)
    let ε := Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1)))
    have hl : r.1.isLeft := by
      have hy' : X.g.severity y.1 ≤ X.p.J n := hy
      change (X.g.roleKey (X.p.J n) y.1).isLeft
      simp only [ChunkGeometry5.roleKey, dite_eq_left hy', Sum.isLeft_inl]
    obtain ⟨μ, hr, _⟩ := hrecord n N E G X L.ht L.elig H ω R y hv
    have hmask := Lane_sol_s05_hist1b.record_mask_mem X r y μ hr
    have hab : ∀ c ∈ r.2.1, arraysOf ω c = Lane_sol_s05_k1.observationArrays X d c :=
      fun c hc => (Lane_sol_s05_k1.observationArrays_eq X r (arraysOf ω) c hc).symm
    have hm : X.step3MassOn H r (arraysOf ω) none ≠ 0 := by
      intro hz
      have hpath := hv.2.2.2.2.2.2.2.2.1
      change 0 < X.step3PostOn H r (arraysOf ω) none (H.2 r.1) at hpath
      simp only [Setup5.step3PostOn, hz, div_zero, lt_self_iff_false] at hpath
    have hm' : X.step3MassOn H r (Lane_sol_s05_k1.observationArrays X d) none ≠ 0 := by
      have he := Lane_sol_s05_hist1b.step3MassOn_arrays_congr X H r (arraysOf ω)
        (Lane_sol_s05_k1.observationArrays X d) hmask hab none
      exact fun hz => hm (he.trans hz)
    have hsource : ∑ x, source d x = 1 := Lane_sol_s05_k1.low_step3Post_sum X H r
      (Lane_sol_s05_k1.observationArrays X d) hl hm'
    let W : Law N :=
      { w := T.completedProxy ε source d
        nonneg := fun x => T.completedRow_nonneg ε source
          (fun d x => Lane_sol_s05_centres.step3Post_nonneg X H d.1
            (Lane_sol_s05_k1.observationArrays X d) (fun _ => x)) (some d) x
        sum_eq_one := T.completedProxy_sum ε source (Real.exp_pos _) d hsource }
    have he (o : X.OddOut) : rowAt R H ω y o = Lane_sol_s05_centres.lowIndexRow W (X.p.s n) o := by
      change (if (o.1 : ℕ) = 0 then T.completedRow ε source
        (Lane_sol_s05_k1.datumIf X r (arraysOf ω)
          (X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H ω R y)) o.2 else 0) = _
      have hd : Lane_sol_s05_k1.datumIf X r (arraysOf ω)
          (X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H ω R y) = some d := by
        simp only [Lane_sol_s05_k1.datumIf, hy, hv, and_self, ite_true, d]
      rw [hd]
      rfl
    simp_rw [he]
    exact Lane_sol_s05_centres.lowIndexRow_sum W (X.p.s n)
  have hrecords (b : X.Base) (hi : X.HighHid) (y : OddRole5 n) (lo : X.LowHid) :
      Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1))) *
        (tab (b, X.joinHidden hi lo) y).experiment.recordBound ≤ 1 := by
    change Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1))) *
      Lane_sol_s05_k1.lookupBudget X C (Lane_sol_s05_k1.positionBudget n L.ht.hp.H) y ≤ 1
    by_cases hy : X.g.low (X.p.J n) y.1
    · rw [Lane_sol_s05_k1.lookupBudget, if_pos hy]
      have hlev : (X.g.roleKey (X.p.J n) y.1).level = X.g.severity y.1 := by
        have hy' : X.g.severity y.1 ≤ X.p.J n := hy
        simp only [ChunkGeometry5.roleKey, dite_eq_left hy', HiddenKey5.level]
      have hnumerical : Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1))) *
          (Real.exp (C * ((X.p.T n : ℝ) * Real.log (X.p.T n) + ((X.g.severity y.1 : ℝ) + 1) * Real.log (X.p.m n) +
            (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ))) *
              (Lane_sol_s05_k1.positionBudget n L.ht.hp.H + 1) ^ X.p.T n) ≤ 1 := by
        simpa only [hXp] using hrecnum L.ht.hp.H hHn (X.g.severity y.1)
      refine le_trans ?_ hnumerical
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg
        (by linarith [Lane_sol_s05_k1.positionBudget_nonneg n L.ht.hp.H]) _)
      unfold Lane_sol_s05_k1.abstractRecordBudget
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [hlev]
      have hmask : (if (X.g.roleKey (X.p.J n) y.1).isLeft ∧ X.g.severity y.1 = X.p.J n then
          (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0) ≤
          (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) := by
        split_ifs <;> first | exact le_rfl | positivity
      linarith only [hmask]
    · simp only [Lane_sol_s05_k1.lookupBudget, hy, ite_false, mul_zero]
      norm_num
  have hcap (R : ℕ) (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n) (o : X.OddOut) :
      (N : ℝ) * rowAt R H ω y o ≤ Real.exp (X.p.DL n) := by
    by_cases hv : X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H ω R y
    · let r := X.actualRecordAt (L.elig H) H ω R y
      have hy : X.g.severity y.1 ≤ X.p.J n := hv.1
      have hl : r.1.isLeft := by
        change (X.g.roleKey (X.p.J n) y.1).isLeft
        simp only [ChunkGeometry5.roleKey, dite_eq_left hy, Sum.isLeft_inl]
      have hlev : r.1.level = X.g.severity y.1 := by
        change (X.g.roleKey (X.p.J n) y.1).level = _
        simp only [ChunkGeometry5.roleKey, dite_eq_left hy, HiddenKey5.level]
      obtain ⟨μ, hr, hids⟩ := hrecord n N E G X L.ht L.elig H ω R y hv.2
      rcases hv.2 with ⟨hb, hstep1, hsel, hcounts, hTid, hhits, hheavy, hraw, hpath, hgate, hpass⟩
      let B : ℝ := X.p.Kcap * ((X.p.q0 : ℝ) * X.p.uSeg n (r.1.level + 1))
      have hprior (x : Fin N) : (N : ℝ) * (X.prior H.1 r.1).w x ≤ Real.exp B := by
        have hnocap := hstep1.2 r.1 (Or.inl ⟨y.1, y.2, rfl⟩)
        by_contra hh
        apply hnocap
        refine ⟨x, ?_⟩
        exact lt_of_not_ge hh
      have hlower : Real.exp (-(X.p.delta * X.p.kPrime n r.1.level)) ≤ X.step3MassOn H r (arraysOf ω) none := by
        have hh := Lane_sol_s05_k1.step3Mass_lower_of_pass X H r (arraysOf ω) hgate hpass
        cases he : r.1 with
        | inl k => simpa only [he, HiddenKey5.level] using hh
        | inr k => simp only [he, Sum.isLeft_inr, Bool.false_eq_true] at hl
      have hstars := Lane_sol_s05_k1.starTypes_card_bound X y hv.1 C hC.le hcount hT2
        (by linarith : (1 : ℝ) ≤ X.p.m n) hpatternX hstarMarginX
      have hO : Lane_sol_s05_k1.observationLength X r ≤ (X.p.m n : ℝ) ^ (61 / 500 : ℝ) := by
        have hh := Lane_sol_s05_k1.observationLength_low_bound X r y μ hr hl hids
          ((X.p.m n : ℝ) ^ (3 / 50 : ℝ)) (by positivity)
          (fun j hj => (hlenX j (by omega)).1)
        have hmpos : (0 : ℝ) < X.p.m n := by linarith
        calc
          _ ≤ (X.p.T n : ℝ) * (Lane_sol_s05_k1.starTypes X y).card * (X.p.m n : ℝ) ^ (3 / 50 : ℝ) := hh
          _ ≤ (X.p.m n : ℝ) ^ (1 / 500 : ℝ) * (X.p.m n : ℝ) ^ (3 / 50 : ℝ) *
              (X.p.m n : ℝ) ^ (3 / 50 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul hTupper hstars (Nat.cast_nonneg _) (by positivity)
          _ = _ := by rw [← Real.rpow_add hmpos, ← Real.rpow_add hmpos]; norm_num
      have hB : B ≤ (X.p.m n : ℝ) ^ (3 / 50 : ℝ) := (hlenX (r.1.level + 1) (by rw [hlev]; omega)).2
      have hk : (X.p.kPrime n (X.g.severity y.1) : ℝ) ≤ (X.p.m n : ℝ) ^ (3 / 50 : ℝ) := by
        have hmin : X.p.kPrime n (X.g.severity y.1) ≤
            X.p.q0 * X.p.uSeg n (X.g.severity y.1) * X.p.lowBlocks n (X.g.severity y.1) :=
          (Nat.min_le_left _ _).trans (Nat.min_le_left _ _)
        exact (Nat.cast_le.mpr hmin).trans (hlenX (X.g.severity y.1) (by omega)).1
      have hbudget := Lane_sol_s05_k1.cap_budget_of_scales X.p n (X.g.severity y.1)
        (by linarith : (1 : ℝ) ≤ X.p.m n) hk B (Lane_sol_s05_k1.observationLength X r) hB
        (by unfold Lane_sol_s05_k1.observationLength; positivity) hO hcapX
      have hpost := Lane_sol_s05_k1.lowPost_cap X H r (arraysOf ω) hl hlower B hprior o.2
      have hrow := mul_le_mul_of_nonneg_left (hrow_bound n N E G X L C hcount hT0 R H ω y o) (Nat.cast_nonneg N)
      calc
        _ ≤ Real.exp (X.p.delta * X.p.kPrime n (X.g.severity y.1)) *
            ((N : ℝ) * X.step3PostOn H r (arraysOf ω) none (fun _ => o.2)) := by convert hrow using 1 <;> ring
        _ ≤ Real.exp (X.p.delta * X.p.kPrime n (X.g.severity y.1)) *
            Real.exp (B + X.p.delta * X.p.kPrime n r.1.level + X.p.a 2 * Lane_sol_s05_k1.observationLength X r) :=
          mul_le_mul_of_nonneg_left hpost (Real.exp_nonneg _)
        _ = Real.exp (B + 2 * X.p.delta * X.p.kPrime n (X.g.severity y.1) +
            X.p.a 2 * Lane_sol_s05_k1.observationLength X r) := by
          rw [hlev, ← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := Real.exp_le_exp.mpr hbudget
    · change (N : ℝ) * (if (o.1 : ℕ) = 0 then (tab H y).completedRow _ _
        (Lane_sol_s05_k1.datumIf X (X.actualRecordAt (L.elig H) H ω R y) (arraysOf ω)
          (X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H ω R y)) o.2 else 0) ≤ _
      simp only [Lane_sol_s05_k1.datumIf, hv, ite_false, Lane_sol_s05_k1.PresentationTable.completedRow, ite_self, mul_zero]
      exact Real.exp_nonneg _
  have hhigh (R : ℕ) (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n) (o : X.OddOut)
      (hy : ¬ X.g.low (X.p.J n) y.1) : rowAt R H ω y o = 0 := by
    simp only [rowAt, row, Lane_sol_s05_k1.datumIf, hy, false_and, ite_false,
      Lane_sol_s05_k1.PresentationTable.completedRow, ite_self]
  have hindex (R : ℕ) (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n) (o : X.OddOut)
      (hi : (o.1 : ℕ) ≠ 0) : rowAt R H ω y o = 0 := by
    change (if (o.1 : ℕ) = 0 then _ else 0) = 0
    rw [if_neg hi]
  have hinvalid (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n) (o : X.OddOut)
      (hv : ¬ L.valid H ω y) : rowAt L.ht.hp.Rlong H ω y o = 0 := by
    have hn : ¬ X.LocalValidAt L.ht L.elig H ω L.ht.hp.Rlong y := fun h => hv ((LL.valid_eq H ω y).mpr h)
    simp only [rowAt, row, Lane_sol_s05_k1.datumIf, hn, and_false, ite_false,
      Lane_sol_s05_k1.PresentationTable.completedRow, ite_self]
  have hdelete (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n)
      (hv : L.valid H ω y) (hy : X.g.low (X.p.J n) y.1)
      (c : L.ht.hp.Loc × X.Ty × Finset (Fin X.blockBound))
      (hc : c ∈ X.refsOn H (X.actualRecord (L.elig H) H ω y) (arraysOf ω)) (o : X.OddOut) :
      rowAt L.ht.hp.Rlong H ω y o ≤ Real.exp (X.p.a 4 * X.refLen c.2.1 c.2.2) *
        X.step3PostOn H (X.actualRecord (L.elig H) H ω y) (arraysOf ω) (some c) (fun _ => o.2) := by
    let r := X.actualRecord (L.elig H) H ω y
    have hlocal := (LL.valid_eq H ω y).mp hv
    have hy' : X.g.severity y.1 ≤ X.p.J n := hy
    have hl : r.1.isLeft := by
      change (X.g.roleKey (X.p.J n) y.1).isLeft
      simp only [ChunkGeometry5.roleKey, dite_eq_left hy', Sum.isLeft_inl]
    have hlev : r.1.level = X.g.severity y.1 := by
      change (X.g.roleKey (X.p.J n) y.1).level = _
      simp only [ChunkGeometry5.roleKey, dite_eq_left hy', HiddenKey5.level]
    obtain ⟨μ, hr, _⟩ := hrecord n N E G X L.ht L.elig H ω L.ht.hp.Rlong y hlocal
    have hlen := Lane_sol_s05_k1.record_refs_length_lower X H r (arraysOf ω) y μ hr hl hT0 c hc
    have hg := hlocal.2.2.2.2.2.2.2.2.2.1
    have hpass := hlocal.2.2.2.2.2.2.2.2.2.2
    have hM : 0 < X.step3MassOn H r (arraysOf ω) none := by
      have hm : X.step3MassOn H r (arraysOf ω) none ≠ 0 := by
        intro hz
        have hpath := hlocal.2.2.2.2.2.2.2.2.1
        change 0 < X.step3PostOn H r (arraysOf ω) none (H.2 r.1) at hpath
        simp only [Setup5.step3PostOn, hz, div_zero, lt_self_iff_false] at hpath
      exact lt_of_le_of_ne (Lane_sol_s05_hist1b.step3MassOn_nonneg X H r (arraysOf ω) none) (Ne.symm hm)
    have hp := Lane_sol_s05_k1.lowPost_delete X H r (arraysOf ω) hl hM hg hpass c hc o.2
    have hrow := hrow_bound n N E G X L C hcount hT0 L.ht.hp.Rlong H ω y o
    have hQ : 0 ≤ X.step3PostOn H r (arraysOf ω) (some c) (fun _ => o.2) := by
      unfold Setup5.step3PostOn
      apply div_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · exact Finset.prod_nonneg (fun h _ => (X.prior H.1 r.1).nonneg o.2)
          · split_ifs <;> norm_num
        · exact Lane_sol_s05_hist1b.obsLikOn_nonneg X H r (arraysOf ω) _ (some c)
      · exact Lane_sol_s05_hist1b.step3MassOn_nonneg X H r (arraysOf ω) (some c)
    have hgap : X.p.a 2 + 2 * X.p.delta ≤ X.p.a 4 := by
      have hdelta := X.p.hdelta.1
      have hh := X.p.hdelta_a (2 : Fin 9) (4 : Fin 9) (by decide)
      linarith
    have hkp : X.p.delta * X.p.kPrime n (X.g.severity y.1) ≤ X.p.delta * X.refLen c.2.1 c.2.2 := by
      rw [hlev] at hlen
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hlen) X.p.hdelta.1.le
    have hcost : X.p.delta * X.p.kPrime n (X.g.severity y.1) +
        (X.p.a 2 + X.p.delta) * X.refLen c.2.1 c.2.2 ≤ X.p.a 4 * X.refLen c.2.1 c.2.2 := by
      have hh := mul_le_mul_of_nonneg_right hgap (Nat.cast_nonneg (X.refLen c.2.1 c.2.2) : (0 : ℝ) ≤ X.refLen c.2.1 c.2.2)
      linarith
    calc
      _ ≤ Real.exp (X.p.delta * X.p.kPrime n (X.g.severity y.1)) *
          X.step3PostOn H r (arraysOf ω) none (fun _ => o.2) := hrow
      _ ≤ Real.exp (X.p.delta * X.p.kPrime n (X.g.severity y.1)) *
          (Real.exp ((X.p.a 2 + X.p.delta) * X.refLen c.2.1 c.2.2) *
            X.step3PostOn H r (arraysOf ω) (some c) (fun _ => o.2)) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
      _ = Real.exp (X.p.delta * X.p.kPrime n (X.g.severity y.1) +
          (X.p.a 2 + X.p.delta) * X.refLen c.2.1 c.2.2) *
            X.step3PostOn H r (arraysOf ω) (some c) (fun _ => o.2) := by rw [← mul_assoc, ← Real.exp_add]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hQ
  have hrow_valid (R : ℕ) (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n) (o : X.OddOut)
      (ho : rowAt R H ω y o ≠ 0) : X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H ω R y := by
    by_contra hv
    apply ho
    simp only [rowAt, row, Lane_sol_s05_k1.datumIf, hv, ite_false,
      Lane_sol_s05_k1.PresentationTable.completedRow, ite_self]
  have hrow_post (R : ℕ) (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n) (o : X.OddOut)
      (ho : rowAt R H ω y o ≠ 0) :
      X.step3PostOn H (X.actualRecordAt (L.elig H) H ω R y) (arraysOf ω) none (fun _ => o.2) ≠ 0 := by
    intro hp
    have hb := hrow_bound n N E G X L C hcount hT0 R H ω y o
    rw [hp, mul_zero] at hb
    exact ho (le_antisymm hb (hrow_nonneg n N E G X L C hcount hT0 R H ω y o))
  have hactual (H : X.KeyHist) (ω : X.CΩ L.ht) (R : ℕ) (y : OddRole5 n) :
      X.actualRecordAt (L.elig H) H ω R y = Lane_sol_s05_k1.recordForChoices X H (arraysOf ω) y
        (fun a => X.selAt (L.elig H) ω R a) := by
    unfold actualRecordAt Lane_sol_s05_k1.recordForChoices
    dsimp only
    apply Prod.ext
    · rfl
    apply Prod.ext
    · ext c; simp only [Finset.mem_biUnion]
    apply Prod.ext
    · ext c; simp only [Finset.mem_biUnion]
    · rfl
  have hactual_congr (R R' : ℕ) (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n)
      (hs : ∀ a ∈ evenNbrs y, X.selAt (L.elig H) ω R a = X.selAt (L.elig H) ω R' a) :
      X.actualRecordAt (L.elig H) H ω R y = X.actualRecordAt (L.elig H) H ω R' y := by
    rw [hactual H ω R y, hactual H ω R' y]
    exact Lane_sol_s05_k1.recordForChoices_congr X H (arraysOf ω) (arraysOf ω) y _ _ hs (fun _ _ _ _ => rfl)
  have hvalid_transfer (R R' : ℕ) (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n)
      (hs : ∀ a ∈ evenNbrs y, X.selAt (L.elig H) ω R a = X.selAt (L.elig H) ω R' a)
      (hv : X.LocalValidAt L.ht L.elig H ω R y) : X.LocalValidAt L.ht L.elig H ω R' y := by
    have hr := hactual_congr R R' H ω y hs
    rcases hv with ⟨hb, hstep1, hsel, hcounts, hids, hhits, hheavy, hraw, hpath, hgate, hpass⟩
    refine ⟨hb, hstep1, ?_, hcounts, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha
      rw [← hs a ha]
      exact hsel a ha
    · have he : (evenNbrs y).image (fun a => X.selAt (L.elig H) ω R a) =
          (evenNbrs y).image (fun a => X.selAt (L.elig H) ω R' a) := Finset.image_congr hs
      rw [← he]
      exact hids
    · intro a ha l k hc hk
      exact hhits a ha l k ((hs a ha).trans hc) hk
    · intro a ha l hc
      exact hheavy a ha l ((hs a ha).trans hc)
    · simpa only [← hr] using hraw
    · simpa only [hr] using hpath
    · simpa only [hr] using hgate
    · simpa only [← hr] using hpass
  have hcongr (R R' : ℕ) (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n)
      (hs : ∀ a ∈ evenNbrs y, X.selAt (L.elig H) ω R a = X.selAt (L.elig H) ω R' a) :
      rowAt R H ω y = rowAt R' H ω y := by
    have hr := hactual_congr R R' H ω y hs
    have hv : X.LocalValidAt L.ht L.elig H ω R y ↔ X.LocalValidAt L.ht L.elig H ω R' y :=
      ⟨hvalid_transfer R R' H ω y hs, hvalid_transfer R' R H ω y (fun a ha => (hs a ha).symm)⟩
    funext o
    simp only [rowAt, row, hr, hv]
  have hmask_ref (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n)
      (hv : X.LocalValidAt L.ht L.elig H ω L.ht.hp.Rlong y) (hy : X.g.low (X.p.J n) y.1)
      (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (l : L.ht.hp.Loc)
      (hs : X.selAt (L.elig H) ω L.ht.hp.Rlong a = some l)
      (ht : (X.g.evenType (X.p.J n) a.1).2.2 = none) :
      (X.actualRecord (L.elig H) H ω y).2.2.2 =
        some (l, X.g.evenType (X.p.J n) a.1, X.refSubset H ω a l) := by
    let r := X.actualRecord (L.elig H) H ω y
    obtain ⟨μ, hr, _⟩ := hrecord n N E G X L.ht L.elig H ω L.ht.hp.Rlong y hv
    have hy' : X.g.severity y.1 ≤ X.p.J n := hy
    have hl : r.1.isLeft := by
      change (X.g.roleKey (X.p.J n) y.1).isLeft
      simp only [ChunkGeometry5.roleKey, dite_eq_left hy', Sum.isLeft_inl]
    have haHigh : X.p.J n < X.g.severity a.1 := by
      by_contra hn
      have hn' : X.g.severity a.1 ≤ X.p.J n := Nat.le_of_not_gt hn
      simp only [ChunkGeometry5.evenType, dite_eq_left hn', Option.some_ne_none] at ht
    cases hm : r.2.2.2 with
    | none =>
      have hh := hr.2.2.2
      have h := hh hl a ha
      simp only [ht, Option.isSome_none, Bool.false_eq_true] at h
    | some e =>
      rcases e with ⟨l0, K0, M⟩
      have hshape := hr.2.2.2
      obtain ⟨_, a0, ha0, hK0, ht0, _, _⟩ := hshape
      have ho := Lane_sol_s05_hist1b.record_mask_mem X r y μ hr (l0, K0) M hm
      change (l0, K0) ∈ (evenNbrs y).biUnion (fun b =>
        match X.selAt (L.elig H) ω L.ht.hp.Rlong b with
        | some l' => {(l', X.g.evenType (X.p.J n) b.1)} | none => ∅) at ho
      obtain ⟨b, hb, hobs⟩ := Finset.mem_biUnion.mp ho
      cases hbsel : X.selAt (L.elig H) ω L.ht.hp.Rlong b with
      | none => simp only [hbsel] at hobs; simp at hobs
      | some lb =>
        have hp : (l0, K0) = (lb, X.g.evenType (X.p.J n) b.1) := by
          simpa only [hbsel, Finset.mem_singleton] using hobs
        cases hp
        have hbHigh : X.p.J n < X.g.severity b.1 := by
          by_contra hn
          have hn' : X.g.severity b.1 ≤ X.p.J n := Nat.le_of_not_gt hn
          simp only [ChunkGeometry5.evenType, dite_eq_left hn', Option.some_ne_none] at ht0
        have hab := Lane_sol_s05_k1.low_high_state_unique X.g X.St y.1 a.1 b.1
          (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hy' haHigh hbHigh
        have hsite : X.siteOf a = X.siteOf b := congrArg X.St.oneHot hab
        have hsel : X.selAt (L.elig H) ω L.ht.hp.Rlong a = X.selAt (L.elig H) ω L.ht.hp.Rlong b := by
          unfold selAt
          rw [hsite]
        have hll : l = lb := Option.some.inj (hs.symm.trans (hsel.trans hbsel))
        subst lb
        have htype : X.g.evenType (X.p.J n) a.1 = X.g.evenType (X.p.J n) b.1 :=
          (X.St.state_determines a.1 b.1 hab).2.2.2.2.1
        rw [← htype] at hm
        cases hk : r.1 with
        | inr k => simp only [hk, Sum.isLeft_inr, Bool.false_eq_true] at hl
        | inl k =>
          have hopt : X.g.optionalKey (X.p.J n) a.1 = some (.inl k) := by
            have hadj := (Finset.mem_filter.mp ha).2
            rcases (L5_1e_cover X.g (X.p.J n)).1 a.1 y.1 hadj with hmem | hopt
            · have hlow := Lane_sol_s05_k1.low_type_of_listed X a.1 r.1 hl (by simpa only [r, actualRecord, actualRecordAt] using hmem)
              exact (not_le_of_gt haHigh hlow).elim
            · have hkey : X.g.roleKey (X.p.J n) y.1 = .inl k := hk
              simpa only [hkey] using hopt
          have hhits := hv.2.2.2.2.2.1 a ha l k hs hopt
          let h0 : Fin (colLen5 (X.p.s n) r.1) := ⟨0, by rw [hk]; decide⟩
          have hgate := hv.2.2.2.2.2.2.2.2.2.1
          have hfirst := (hgate.2 (l, X.g.evenType (X.p.J n) a.1) M hm h0).2
          rw [Lane_sol_s05_k1.low_column_eval X H r.1 k hk h0] at hfirst
          have href : X.refSubset H ω a l = M := by
            simp only [refSubset, Setup5.refSubsetOn, ht, hopt, hhits, ite_true]
            exact hfirst
          rw [hm, href]
  have hsupport (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n) (o : X.OddOut)
      (ho : rowAt L.ht.hp.Rlong H ω y o ≠ 0) (a : EvenRole5 n) (ha : a ∈ evenNbrs y)
      (c : X.CRef L.ht) (hc : X.evenRefOf (L.elig H) H ω a = some c)
      (z : X.Block (X.g.evenType (X.p.J n) a.1)) (hz : z ∈ X.refBlocks ω a c) :
      X.BlockHits _ z o.2 := by
    obtain ⟨hy, hv⟩ := hrow_valid L.ht.hp.Rlong H ω y o ho
    have hpost := hrow_post L.ht.hp.Rlong H ω y o ho
    let r := X.actualRecord (L.elig H) H ω y
    have hy' : X.g.severity y.1 ≤ X.p.J n := hy
    have hl : r.1.isLeft := by
      change (X.g.roleKey (X.p.J n) y.1).isLeft
      simp only [ChunkGeometry5.roleKey, dite_eq_left hy', Sum.isLeft_inl]
    cases hs : X.selLong (L.elig H) ω a with
    | none => simp [evenRefOf, hs] at hc
    | some l =>
      have he : c = (l, X.refSubset H ω a l) := by simpa only [evenRefOf, hs, Option.map_some, Option.some.injEq] using hc.symm
      subst c
      have hsa : X.selAt (L.elig H) ω L.ht.hp.Rlong a = some l := hs
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hobs : (l, X.g.evenType (X.p.J n) a.1) ∈ r.2.1 := by
        apply Finset.mem_biUnion.mpr
        exact ⟨a, ha, by simp only [hsa, Finset.mem_singleton]⟩
      by_cases haLow : X.g.severity a.1 ≤ X.p.J n
      · have hmem : r.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 := by
          rcases (L5_1e_cover X.g (X.p.J n)).1 a.1 y.1 (Finset.mem_filter.mp ha).2 with hk | hk
          · exact hk
          · simp only [ChunkGeometry5.optionalKey] at hk
            have hn : X.g.severity a.1 ≠ X.p.J n + 1 := by omega
            simp [hn] at hk
        have hpref : X.p.typeSegs n (X.g.evenType (X.p.J n) a.1) ≤ X.p.uSeg n (r.1.level + 1) := by
          have hlev : r.1.level = X.g.severity y.1 := by
            change (X.g.roleKey (X.p.J n) y.1).level = _
            simp only [ChunkGeometry5.roleKey, dite_eq_left hy', HiddenKey5.level]
          have hadj := Lane_sol_s05_h5l.adjacent_severity X.g a.1 y.1 (Finset.mem_filter.mp ha).2
          simp only [Params5.typeSegs, ChunkGeometry5.evenType, dite_eq_left haLow, hlev]
          exact Lane_q_s05_hist1b.uSeg_mono5 X.p n _ _ hadj.1
        exact Lane_sol_s05_k1.lowPost_observed_hits X H r (arraysOf ω) hl hv.1
          (l, X.g.evenType (X.p.J n) a.1) hobs hmem (hcoarse a.1 r.1 hmem) hpref i
          (hv.2.2.2.2.2.2.2.1 _ hobs i) o.2 hpost
      · have ht : (X.g.evenType (X.p.J n) a.1).2.2 = none := by simp only [ChunkGeometry5.evenType, dite_eq_right haLow]
        have hm := hmask_ref H ω y hv hy a ha l hsa ht
        obtain ⟨j, hj, hji⟩ := (Finset.mem_filter.mp hi).2
        exact Lane_sol_s05_k1.lowPost_mask_hits X H r (arraysOf ω) hl
          (l, X.g.evenType (X.p.J n) a.1) (X.refSubset H ω a l) hm o.2 hpost j hj i hji
  have hlong_local (H : X.KeyHist) (y : OddRole5 n) : FinProb.DependsOn
      (fun ω => rowAt L.ht.hp.Rlong H ω y) (X.scopeBall (h := L.ht) y.1 (L.ht.hp.r + L.slack)) := by
    intro ω ω' hω
    let q := X.St.oneHot (X.St.stateOf y.1)
    have hscope (l : L.ht.hp.Loc) (hl : HypercubeRamsey.hammingDist l.1 q ≤ L.ht.hp.r + L.slack) : ω l = ω' l :=
      hω l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa only [q] using hl⟩)
    have hsel (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
        X.selAt (L.elig H) ω L.ht.hp.Rlong a = X.selAt (L.elig H) ω' L.ht.hp.Rlong a := by
      let v := X.siteOf a
      have hbudget : _root_.hammingDist v q + L.ht.hp.Rlong + 16 ≤ L.slack := by
        simpa only [Lane_sol_s05_k1.cube_hamming_eq] using L.slack_nbr y a ha
      change L.ht.hp.selectionAt (X.sites L.ht) (pos ω) (act ω) (L.elig H ω) (tie ω) L.ht.hp.Rlong v =
        L.ht.hp.selectionAt (X.sites L.ht) (pos ω') (act ω') (L.elig H ω') (tie ω') L.ht.hp.Rlong v
      apply Lane_sol_s05_k1.selectionAt_local
      · intro s hs j
        apply L.elig_local H s j ω ω'
        intro l hl
        have hls : _root_.hammingDist l.1 s ≤ L.ht.hp.r + 16 := by
          simpa only [Lane_sol_s05_k1.cube_hamming_eq] using (Finset.mem_filter.mp hl).2
        apply hscope l
        have h1 := _root_.hammingDist_triangle l.1 s v
        have h2 := _root_.hammingDist_triangle l.1 v q
        simp only [← Lane_sol_s05_k1.cube_hamming_eq_with] at hbudget hls hs h1 h2 ⊢
        omega
      · intro s hs j l hl
        simpa only [Lane_sol_s05_k1.cube_hamming_eq] using (L.elig_shape H ω s j l hl).2.2
      · intro l hl
        have hb : HypercubeRamsey.hammingDist l.1 q ≤ L.ht.hp.r + L.slack := by
          have ht := _root_.hammingDist_triangle l.1 v q
          change _root_.hammingDist l.1 v ≤ L.ht.hp.Rlong + L.ht.hp.r + 8 at hl
          simp only [← Lane_sol_s05_k1.cube_hamming_eq_with] at hbudget hl ht ⊢
          omega
        exact congrArg (fun z : X.CVal L.ht => z.1) (hscope l hb)
      · intro l hl
        have hb : HypercubeRamsey.hammingDist l.1 q ≤ L.ht.hp.r + L.slack := by
          have ht := _root_.hammingDist_triangle l.1 v q
          change _root_.hammingDist l.1 v ≤ L.ht.hp.Rlong + L.ht.hp.r + 8 at hl
          simp only [← Lane_sol_s05_k1.cube_hamming_eq_with] at hbudget hl ht ⊢
          omega
        exact congrArg (fun z : X.CVal L.ht => z.2.1) (hscope l hb)
      · intro j
        have hb : HypercubeRamsey.hammingDist (v, j).1 q ≤ L.ht.hp.r + L.slack := by
          dsimp only
          simp only [← Lane_sol_s05_k1.cube_hamming_eq_with] at hbudget ⊢
          omega
        exact congrArg (fun z : X.CVal L.ht => z.2.2.1) (hscope (v, j) hb)
    have harr (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (l : L.ht.hp.Loc)
        (hs : X.selAt (L.elig H) ω L.ht.hp.Rlong a = some l) :
        arraysOf ω (l, X.g.evenType (X.p.J n) a.1) = arraysOf ω' (l, X.g.evenType (X.p.J n) a.1) := by
      have hd := (hselected n N E G X L H ω L.ht.hp.Rlong a l hs).2
      have hbudget : _root_.hammingDist (X.siteOf a) q + L.ht.hp.Rlong + 16 ≤ L.slack := by
        simpa only [Lane_sol_s05_k1.cube_hamming_eq] using L.slack_nbr y a ha
      have hb : HypercubeRamsey.hammingDist l.1 q ≤ L.ht.hp.r + L.slack := by
        have ht := _root_.hammingDist_triangle l.1 (X.siteOf a) q
        simp only [← Lane_sol_s05_k1.cube_hamming_eq_with] at hbudget hd ht ⊢
        omega
      exact congrArg (fun z : X.CVal L.ht => z.2.2.2 (X.g.evenType (X.p.J n) a.1)) (hscope l hb)
    have hr : X.actualRecord (L.elig H) H ω y = X.actualRecord (L.elig H) H ω' y := by
      rw [actualRecord, actualRecord, hactual H ω L.ht.hp.Rlong y, hactual H ω' L.ht.hp.Rlong y]
      exact Lane_sol_s05_k1.recordForChoices_congr X H (arraysOf ω) (arraysOf ω') y _ _ hsel harr
    have hobs : ∀ c ∈ (X.actualRecord (L.elig H) H ω y).2.1, arraysOf ω c = arraysOf ω' c := by
      intro c hc
      obtain ⟨a, ha, hc⟩ := Finset.mem_biUnion.mp hc
      cases hs : X.selAt (L.elig H) ω L.ht.hp.Rlong a with
      | none => simp only [hs] at hc; simp at hc
      | some l =>
        have he : c = (l, X.g.evenType (X.p.J n) a.1) := by simpa only [hs, Finset.mem_singleton] using hc
        rw [he]
        exact harr a ha l hs
    have hd : Lane_sol_s05_k1.observationDatum X (X.actualRecord (L.elig H) H ω y) (arraysOf ω) =
        Lane_sol_s05_k1.observationDatum X (X.actualRecord (L.elig H) H ω' y) (arraysOf ω') :=
      (Lane_sol_s05_k1.observationDatum_record_eq_iff X _ _ _ _).mpr ⟨hr, hobs⟩
    have hvalid : X.LocalValidAt L.ht L.elig H ω L.ht.hp.Rlong y ↔
        X.LocalValidAt L.ht L.elig H ω' L.ht.hp.Rlong y :=
      (LL.valid_eq H ω y).symm.trans ((Iff.of_eq (L.valid_local H y ω ω' hω)).trans (LL.valid_eq H ω' y))
    have hp : Lane_sol_s05_k1.datumIf X (X.actualRecord (L.elig H) H ω y) (arraysOf ω)
        (X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H ω L.ht.hp.Rlong y) =
        Lane_sol_s05_k1.datumIf X (X.actualRecord (L.elig H) H ω' y) (arraysOf ω')
        (X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H ω' L.ht.hp.Rlong y) := by
      unfold Lane_sol_s05_k1.datumIf
      rw [hvalid]
      split_ifs
      · exact congrArg some hd
      · rfl
    funext o
    change (if (o.1 : ℕ) = 0 then (tab H y).completedRow _ _
      (Lane_sol_s05_k1.datumIf X (X.actualRecord (L.elig H) H ω y) (arraysOf ω)
        (X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H ω L.ht.hp.Rlong y)) o.2 else 0) =
      (if (o.1 : ℕ) = 0 then (tab H y).completedRow _ _
      (Lane_sol_s05_k1.datumIf X (X.actualRecord (L.elig H) H ω' y) (arraysOf ω')
        (X.g.low (X.p.J n) y.1 ∧ X.LocalValidAt L.ht L.elig H ω' L.ht.hp.Rlong y)) o.2 else 0)
    rw [hp]
  have htable_mass (H : X.KeyHist) (y : OddRole5 n) (hy : X.g.low (X.p.J n) y.1)
      (x : Fin N) (d : Lane_sol_s05_k1.ObservationDatum X (Id := L.ht.hp.Loc)) :
      Lane_sol_s05_k1.presentationMass (tab H y).raw (tab H y).present x d =
        X.shortPresentationMass L (X.withCol H (X.g.roleKey (X.p.J n) y.1) (fun _ => x)) y d.1
          (Lane_sol_s05_k1.observationArrays X d) := by
    let Hcand := fun x : Fin N => X.withCol H (X.g.roleKey (X.p.J n) y.1) (fun _ => x)
    let record := fun x ω => X.actualRecordAt (L.elig (Hcand x)) (Hcand x) ω (L.ht.hp.Rshort (X.p.m n)) y
    let valid := fun x ω => X.g.low (X.p.J n) y.1 ∧
      X.LocalValidAt L.ht L.elig (Hcand x) ω (L.ht.hp.Rshort (X.p.m n)) y
    have hm := Lane_sol_s05_k1.observationPresentation_mass X record (fun _ ω => arraysOf ω) valid
      (fun x => X.centreLaw L.ht (Hcand x)) x d.1 (Lane_sol_s05_k1.observationArrays X d)
    rw [Lane_sol_s05_k1.observationDatum_reconstruct] at hm
    change Lane_sol_s05_k1.presentationMass (tab H y).raw (tab H y).present x d = _ at hm
    simpa only [valid, hy, true_and, record, Hcand, shortPresentationMass] using hm
  have hmean_expand (H : X.KeyHist) (y : OddRole5 n) (hy : X.g.low (X.p.J n) y.1) (x : Fin N) :
      (X.centreLaw L.ht H).expect
        (fun ω => (N : ℝ) * rowAt (L.ht.hp.Rshort (X.p.m n)) H ω y (0, x)) =
        (N : ℝ) * ∑ d : Lane_sol_s05_k1.ObservationDatum X (Id := L.ht.hp.Loc),
          X.shortPresentationMass L H y d.1 (Lane_sol_s05_k1.observationArrays X d) *
            (tab H y).completedProxy (Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1))))
              (fun d x => X.step3PostOn H d.1 (Lane_sol_s05_k1.observationArrays X d) none (fun _ => x)) d x := by
    let ℓ := X.g.roleKey (X.p.J n) y.1
    have hl : ℓ.isLeft := by
      have hy' : X.g.severity y.1 ≤ X.p.J n := hy
      simp only [ℓ, ChunkGeometry5.roleKey, dite_eq_left hy', Sum.isLeft_inl]
    obtain ⟨z, hz⟩ := Lane_sol_s05_k1.low_column_const X ℓ hl (H.2 ℓ)
    have hH : X.withCol H ℓ (fun _ => z) = H := by
      rw [← hz]
      exact Lane_sol_s05_k1.withCol_current X H ℓ
    let T := tab H y
    let ε := Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1)))
    let source := fun d : Lane_sol_s05_k1.ObservationDatum X (Id := L.ht.hp.Loc) =>
      fun x => X.step3PostOn H d.1 (Lane_sol_s05_k1.observationArrays X d) none (fun _ => x)
    have hr : T.raw z = X.centreLaw L.ht H := by
      change X.centreLaw L.ht (X.withCol H ℓ (fun _ => z)) = _
      rw [hH]
    have hp (ω : X.CΩ L.ht) (x : Fin N) : rowAt (L.ht.hp.Rshort (X.p.m n)) H ω y (0, x) =
        T.completedRow ε source (T.present z ω) x := by
      have hh := hrow_short n N E G X L C hcount hT0 H y z ω x
      rw [hH] at hh
      exact hh
    have he := Lane_sol_s05_k1.expect_completed_external T ε (N : ℝ) source (X.centreLaw L.ht H)
      (fun ω x => rowAt (L.ht.hp.Rshort (X.p.m n)) H ω y (0, x)) z x hr hp
    simp_rw [htable_mass H y hy z, hH] at he
    exact he
  have hmass_impossible (H : X.KeyHist) (y : OddRole5 n)
      (d : Lane_sol_s05_k1.ObservationDatum X (Id := L.ht.hp.Loc))
      (hd : ¬ ∃ μ, X.RecordFrom d.1 y μ) :
      X.shortPresentationMass L H y d.1 (Lane_sol_s05_k1.observationArrays X d) = 0 := by
    unfold shortPresentationMass FinProb.pr
    apply Finset.sum_eq_zero
    intro ω _
    apply if_neg
    rintro ⟨hv, hr, _⟩
    obtain ⟨μ, hμ, _⟩ := hrecord n N E G X L.ht L.elig H ω (L.ht.hp.Rshort (X.p.m n)) y hv
    exact hd ⟨μ, hr ▸ hμ⟩
  sorry

set_option maxHeartbeats 2000000 in
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
  classical
  intro cL cH hc Ckey
  let R : ParamReq5 := {
    Kcap := fun _ => 0
    Kpp := fun _ => 0
    Kh := fun _ => 0
    K1 := fun _ => 0
    K2 := fun _ => 0
    KD := fun _ => 0
    Ks := fun _ => 0
    KB := fun _ => 0
    alpha := fun _ => 1 / 50
    alpha_pos := fun _ => by norm_num }
  refine ⟨R, ?_⟩
  intro p hpR
  have hmTop : Filter.Tendsto (fun n : ℕ => (p.m n : ℝ)) Filter.atTop Filter.atTop :=
    Lane_sol_s05_h1.tendsto_m p
  have hTheta : (0.9 : ℝ) < 1 - p.alpha / 100000 := by
    have := p.halpha.2
    norm_num at this ⊢ <;> linarith
  have hAlpha : 0 < p.alpha ∧ p.alpha < 2 * (1 - p.alpha / 100000) := by
    constructor
    · exact p.halpha.1
    · have := p.halpha.2
      norm_num at this ⊢ <;> linarith
  obtain ⟨nHeight, hHeight⟩ := height_selection_short
    10 (p.alpha / 10000) (p.alpha / 2000) (p.alpha / 1000000) (p.alpha / 100000)
    (1 - p.alpha / 100000) (p.alpha / 20000) (1 / 2) 2 p.alpha 8
    (Lane_sol_s05_centres.height_admissible p)
    (Lane_sol_s05_centres.heightRegime p) hTheta hAlpha
  obtain ⟨nReg, hReg⟩ := Filter.eventually_atTop.mp
    (Lane_sol_s05_centres.height_regime_eventually p)
  have hscale : Filter.Eventually (fun n : ℕ =>
      Real.exp (p.DL n) * Real.exp (-Real.sqrt n) ≤ 1 / 2 ∧
      (n : ℝ) * Real.exp (p.DL n) *
        Real.exp (-3 * (p.m n : ℝ) ^ ((1 : ℝ) / 5)) ≤ 1 / 2) Filter.atTop := by
    have hlogSmall : Filter.Eventually (fun n : ℕ =>
        Real.log (n : ℝ) ≤ (n : ℝ) ^ (p.alpha / 10)) Filter.atTop := by
      have hlittle := ((isLittleO_log_rpow_atTop
          (div_pos p.halpha.1 (by norm_num : (0 : ℝ) < 10))).comp_tendsto
        tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1)
      filter_upwards [hlittle, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
      simpa only [Function.comp_apply, Real.norm_eq_abs, one_mul,
        abs_of_nonneg hlog0,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hn
    have hlogM : Filter.Eventually (fun n : ℕ =>
        Real.log (n : ℝ) ≤ (p.m n : ℝ) ^ ((1 : ℝ) / 5)) Filter.atTop := by
      filter_upwards [hlogSmall, Filter.eventually_ge_atTop (1 : ℕ)] with n hlog hn1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hnpos : (0 : ℝ) < n := by positivity
      have hmLower : (n : ℝ) ^ p.alpha ≤ (p.m n : ℝ) := by
        dsimp [Params5.m]
        exact_mod_cast (Nat.le_ceil ((n : ℝ) ^ p.alpha))
      have hpowEq : (n : ℝ) ^ (p.alpha / 5) =
          ((n : ℝ) ^ p.alpha) ^ ((1 : ℝ) / 5) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg n)]
        congr 1 <;> ring
      have hpow : (n : ℝ) ^ (p.alpha / 10) ≤
          (n : ℝ) ^ (p.alpha / 5) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
      calc
        Real.log (n : ℝ) ≤ (n : ℝ) ^ (p.alpha / 10) := hlog
        _ ≤ (n : ℝ) ^ (p.alpha / 5) := hpow
        _ = ((n : ℝ) ^ p.alpha) ^ ((1 : ℝ) / 5) := hpowEq
        _ ≤ (p.m n : ℝ) ^ ((1 : ℝ) / 5) :=
          Real.rpow_le_rpow (by positivity) hmLower (by norm_num)
    have hDLsmall : Filter.Eventually (fun n : ℕ =>
        p.DL n ≤ (p.m n : ℝ) ^ ((1 : ℝ) / 5) / 2) Filter.atTop := by
      have hpowTop : Filter.Tendsto (fun n : ℕ => (p.m n : ℝ) ^ ((1 : ℝ) / 20))
          Filter.atTop Filter.atTop :=
        (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hmTop
      filter_upwards [hpowTop.eventually_ge_atTop 2,
          Filter.eventually_ge_atTop (1 : ℕ)] with n hpow hn1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hmLower : (n : ℝ) ^ p.alpha ≤ (p.m n : ℝ) := by
        dsimp [Params5.m]
        exact_mod_cast (Nat.le_ceil ((n : ℝ) ^ p.alpha))
      have hmge : (1 : ℝ) ≤ (p.m n : ℝ) :=
        (Real.one_le_rpow hnR p.halpha.1.le).trans hmLower
      have hmpos : (0 : ℝ) < (p.m n : ℝ) := lt_of_lt_of_le (by norm_num) hmge
      have hmul : (p.m n : ℝ) ^ ((1 : ℝ) / 20) *
          (p.m n : ℝ) ^ (15 / 100 : ℝ) =
            (p.m n : ℝ) ^ ((1 : ℝ) / 5) := by
        rw [← Real.rpow_add hmpos] <;> congr 1 <;> norm_num
      have hineq := mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg (Nat.cast_nonneg (p.m n)) (15 / 100 : ℝ))
      rw [hmul] at hineq
      have hDL : p.DL n = (p.m n : ℝ) ^ (15 / 100 : ℝ) := rfl
      rw [hDL]
      nlinarith
    have hDLsqrt : Filter.Eventually (fun n : ℕ =>
        p.DL n ≤ Real.sqrt n / 2) Filter.atTop := by
      have hMargin := Lane_sol_s05_centres.nat_power_margin
        (2 * (2 : ℝ) ^ (15 / 100 : ℝ)) (p.alpha * (15 / 100 : ℝ))
        (1 / 2 : ℝ) (by nlinarith [p.halpha.2])
      filter_upwards [hMargin, Filter.eventually_ge_atTop (1 : ℕ)] with n hmargin hn1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hnpos : (0 : ℝ) < n := by positivity
      have hmUpper : (p.m n : ℝ) ≤ 2 * (n : ℝ) ^ p.alpha := by
        dsimp [Params5.m]
        have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) p.alpha)
        change (⌈(n : ℝ) ^ p.alpha⌉₊ : ℝ) < _ at hceil
        have hpow : (1 : ℝ) ≤ (n : ℝ) ^ p.alpha :=
          Real.one_le_rpow hnR p.halpha.1.le
        linarith
      have hmnonneg : 0 ≤ (p.m n : ℝ) := Nat.cast_nonneg _
      have hpowUpper := Real.rpow_le_rpow hmnonneg hmUpper
        (by norm_num : 0 ≤ (15 / 100 : ℝ))
      have hpowEq : (2 * (n : ℝ) ^ p.alpha) ^ (15 / 100 : ℝ) =
          2 ^ (15 / 100 : ℝ) * (n : ℝ) ^ (p.alpha * (15 / 100 : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _),
          ← Real.rpow_mul (Nat.cast_nonneg n)]
      have hDL : p.DL n = (p.m n : ℝ) ^ (15 / 100 : ℝ) := rfl
      have hcap : 2 * p.DL n ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [hDL]
        calc
          _ ≤ 2 * (2 * (n : ℝ) ^ p.alpha) ^ (15 / 100 : ℝ) :=
            mul_le_mul_of_nonneg_left hpowUpper (by norm_num)
          _ = 2 * 2 ^ (15 / 100 : ℝ) *
              (n : ℝ) ^ (p.alpha * (15 / 100 : ℝ)) := by rw [hpowEq]; ring
          _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := hmargin
      have hcapSqrt : 2 * p.DL n ≤ Real.sqrt n := by
        simpa only [Real.sqrt_eq_rpow] using hcap
      nlinarith
    have hexpNegOne : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
      have hExpOne : (2 : ℝ) ≤ Real.exp 1 := by
        linarith [Real.add_one_le_exp (1 : ℝ)]
      rw [Real.exp_neg]
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num) hExpOne
    filter_upwards [hlogM, hDLsmall, hDLsqrt,
        Filter.eventually_ge_atTop (4 : ℕ)] with n hlog hDLm hDLs hn4
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hMge : (1 : ℝ) ≤ (p.m n : ℝ) ^ ((1 : ℝ) / 5) := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hmLower : (n : ℝ) ^ p.alpha ≤ (p.m n : ℝ) := by
        dsimp [Params5.m]
        exact_mod_cast (Nat.le_ceil ((n : ℝ) ^ p.alpha))
      have hmge : (1 : ℝ) ≤ (p.m n : ℝ) :=
        (Real.one_le_rpow hn1 p.halpha.1.le).trans hmLower
      exact Real.one_le_rpow hmge (by norm_num)
    have hroot : (2 : ℝ) ≤ Real.sqrt n := by
      calc
        (2 : ℝ) = Real.sqrt 4 := by norm_num
        _ ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast (show 4 ≤ n by omega))
    have hfirst : p.DL n - Real.sqrt n ≤ -1 := by nlinarith
    have hfirstEq : Real.exp (p.DL n) * Real.exp (-Real.sqrt n) =
        Real.exp (p.DL n - Real.sqrt n) := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    have hsecondExp : Real.log (n : ℝ) + p.DL n -
        3 * (p.m n : ℝ) ^ ((1 : ℝ) / 5) ≤ -1 := by nlinarith
    have hsecondEq : (n : ℝ) * Real.exp (p.DL n) *
        Real.exp (-3 * (p.m n : ℝ) ^ ((1 : ℝ) / 5)) =
          Real.exp (Real.log (n : ℝ) + p.DL n -
            3 * (p.m n : ℝ) ^ ((1 : ℝ) / 5)) := by
      calc
        _ = Real.exp (Real.log (n : ℝ)) * Real.exp (p.DL n) *
            Real.exp (-3 * (p.m n : ℝ) ^ ((1 : ℝ) / 5)) := by
          rw [Real.exp_log hnpos]
        _ = Real.exp (Real.log (n : ℝ) + p.DL n -
            3 * (p.m n : ℝ) ^ ((1 : ℝ) / 5)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1 <;> ring
    refine ⟨?_, ?_⟩
    · calc
        _ = Real.exp (p.DL n - Real.sqrt n) := hfirstEq
        _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr hfirst
        _ ≤ 1 / 2 := hexpNegOne
    · calc
        _ = Real.exp (Real.log (n : ℝ) + p.DL n -
            3 * (p.m n : ℝ) ^ ((1 : ℝ) / 5)) := hsecondEq
        _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr hsecondExp
        _ ≤ 1 / 2 := hexpNegOne
  obtain ⟨nScale, hscaleAt⟩ := Filter.eventually_atTop.mp hscale
  let n₀ := max nScale (max nHeight nReg)
  refine ⟨n₀, ?_⟩
  intro n hn N E G X hXp L hL Cloc T H hH y x hy
  subst p
  dsimp [n₀] at hn
  have hnScale : nScale ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hnInner : max nHeight nReg ≤ n :=
    le_trans (Nat.le_max_right nScale (max nHeight nReg)) hn
  have hnHeight : nHeight ≤ n := le_trans (Nat.le_max_left nHeight nReg) hnInner
  have hnReg : nReg ≤ n := le_trans (Nat.le_max_right nHeight nReg) hnInner
  have hscaleN := hscaleAt n hnScale
  obtain ⟨hdimLo, hdimHi, hreg⟩ := hReg n hnReg (X.p.m n) (X.p.J n) X.g X.St
  let LocalArrays := ∀ K : X.Ty, X.Array K
  let CurriedArrays := L.ht.hp.Loc → LocalArrays
  let aux := L.ht.hp.Ties × CurriedArrays
  let locPosLaw : L.ht.hp.Loc → FinProb Bool := fun _ =>
    FinProb.bernoulli (L.ht.hp.lam / (L.ht.hp.V : ℝ))
  let locActLaw : L.ht.hp.Loc → FinProb Bool := fun _ =>
    FinProb.bernoulli ((n : ℝ) ^ L.ht.b₀ / L.ht.hp.lam)
  let locTieLaw : L.ht.hp.Loc → FinProb L.ht.hp.TiePerm := fun _ =>
    FinProb.uniformAll (Ω := L.ht.hp.TiePerm) ⟨1⟩
  let locArrayLaw : L.ht.hp.Loc → FinProb LocalArrays := fun _ =>
    FinProb.pi fun K : X.Ty =>
      FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K
  let arrayLaw : FinProb CurriedArrays := FinProb.pi locArrayLaw
  let auxLaw : FinProb aux := FinProb.prod L.ht.hp.tieLaw arrayLaw
  let splitTo : X.CΩ L.ht →
      ((L.ht.hp.Loc → Bool) × aux) × (L.ht.hp.Loc → Bool) := fun ω =>
    ((X.pos ω, ((fun l => (ω l).2.2.1), fun l K => (ω l).2.2.2 K)), X.act ω)
  let splitFrom : (((L.ht.hp.Loc → Bool) × aux) × (L.ht.hp.Loc → Bool)) →
      X.CΩ L.ht := fun z l => (z.1.1 l, (z.2 l, (z.1.2.1 l, z.1.2.2 l)))
  have splitLeft : ∀ ω, splitFrom (splitTo ω) = ω := by
    intro ω
    funext l
    cases hωl : ω l with
    | mk P t => cases t with
      | mk A t => cases t with
        | mk τ D =>
          calc
            splitFrom (splitTo ω) l = ω l := by
              simp [splitFrom, splitTo, Setup5.pos, Setup5.act] <;> exact hωl
            _ = (P, A, τ, D) := hωl
  have splitRight : ∀ z, splitTo (splitFrom z) = z := by
    intro z
    cases z with
    | mk q A => cases q with
      | mk P t => cases t with
        | mk τ D => rfl
  let split : X.CΩ L.ht ≃
      ((L.ht.hp.Loc → Bool) × aux) × (L.ht.hp.Loc → Bool) := {
    toFun := splitTo
    invFun := splitFrom
    left_inv := splitLeft
    right_inv := splitRight }
  let productLaw : FinProb (((L.ht.hp.Loc → Bool) × aux) × (L.ht.hp.Loc → Bool)) :=
    FinProb.prod (FinProb.prod L.ht.hp.posLaw auxLaw) L.ht.hp.actLaw
  have hsplitWeights : (FinProb.map (X.centreLaw L.ht H) split).w = productLaw.w := by
    funext z
    have hmw : (FinProb.map (X.centreLaw L.ht H) split).w z =
        (X.centreLaw L.ht H).w (split.symm z) := by
      unfold FinProb.map
      have hiff (ω : X.CΩ L.ht) : split ω = z ↔ ω = split.symm z := by
        constructor
        · intro h
          apply split.injective
          simpa using h
        · intro h
          simpa [h]
      simp [hiff]
    rw [hmw]
    cases z with
    | mk q A => cases q with
      | mk P t => cases t with
        | mk τ D =>
          change (∏ l : L.ht.hp.Loc,
              (locPosLaw l).w (P l) *
                ((locActLaw l).w (A l) *
                  ((locTieLaw l).w (τ l) * (locArrayLaw l).w (D l)))) =
            ((∏ l : L.ht.hp.Loc, (locPosLaw l).w (P l)) *
              ((∏ l : L.ht.hp.Loc, (locTieLaw l).w (τ l)) *
                (∏ l : L.ht.hp.Loc, (locArrayLaw l).w (D l)))) *
              (∏ l : L.ht.hp.Loc, (locActLaw l).w (A l))
          simp only [Finset.prod_mul_distrib] <;> ring_nf
  have hsplitLaw : FinProb.map (X.centreLaw L.ht H) split = productLaw := by
    cases hmap : FinProb.map (X.centreLaw L.ht H) split with
    | mk pw pn ps =>
      cases hprod : productLaw with
      | mk qw qn qs =>
        have hw : pw = qw := by
          have h := hsplitWeights
          rw [hmap, hprod] at h
          exact h
        subst qw
        rfl
  rcases L.ht.fixed with ⟨hb₀, hb, hσ, hζ, hθ, ha⟩
  have hHpH : L.ht.hp.H =
      topScale n (X.p.alpha / 1000000) (X.p.alpha / 100000) := by
    dsimp [Setup5.HeightChoice5.hp]
    rw [hσ, hζ]
  have hHpB₀ : L.ht.hp.b₀ = X.p.alpha / 10000 := by
    simpa [Setup5.HeightChoice5.hp] using hb₀
  have hHpB : L.ht.hp.b = X.p.alpha / 2000 := by
    simpa [Setup5.HeightChoice5.hp] using hb
  let Esel : (L.ht.hp.Loc → Bool) → aux → L.ht.hp.EligMap := fun P au =>
    L.elig H (split.symm ((P, au), fun _ => false))
  let siteQuery : EvenRole5 n → CubeVertex L.ht.hp.d :=
    fun a => (show CubeVertex L.ht.hp.d from X.siteOf a)
  have siteQuery_eq (a : EvenRole5 n) : siteQuery a = X.siteOf a := by
    simp [siteQuery, Setup5.HeightChoice5.hp, Setup5.siteOf]
  let mismatchT : (((L.ht.hp.Loc → Bool) × aux) × (L.ht.hp.Loc → Bool)) →
      EvenRole5 n → Prop := fun z a =>
        L.ht.hp.height (X.sites L.ht) z.1.1 z.2 (Esel z.1.1 z.1.2)
            L.ht.hp.Rlong (siteQuery a) ≠
          L.ht.hp.height (X.sites L.ht) z.1.1 z.2 (Esel z.1.1 z.1.2)
            (L.ht.hp.Rshort (X.p.m n)) (siteQuery a)
  let legalT : (((L.ht.hp.Loc → Bool) × aux) × (L.ht.hp.Loc → Bool)) → Prop :=
    fun z => L.ht.hp.Legal z.1.1 (Esel z.1.1 z.1.2) (X.sites L.ht)
  let mismatch : X.CΩ L.ht → EvenRole5 n → Prop := fun ω a =>
    L.ht.hp.height (X.sites L.ht) (X.pos ω) (X.act ω) (L.elig H ω)
        L.ht.hp.Rlong (siteQuery a) ≠
      L.ht.hp.height (X.sites L.ht) (X.pos ω) (X.act ω) (L.elig H ω)
        (L.ht.hp.Rshort (X.p.m n)) (siteQuery a)
  have selectionAtEq {q : HDParams} (S : q.Sites) (P A : q.Loc → Bool)
      (F : q.EligMap) (τ : q.Ties) (R R' : ℕ) (v : CubeVertex q.d)
      (hh : q.height S P A F R v = q.height S P A F R' v) :
      q.selectionAt S P A F τ R v = q.selectionAt S P A F τ R' v := by
    simp [HDParams.selectionAt, hh]
  have hEsel (ω : X.CΩ L.ht) :
      Esel (X.pos ω) ((fun l => (ω l).2.2.1), fun l K => (ω l).2.2.2 K) =
        L.elig H ω := by
    let ω' := splitFrom
      (((X.pos ω, ((fun l => (ω l).2.2.1), fun l K => (ω l).2.2.2 K)), fun _ => false))
    have hpre : ∀ l, (ω' l).1 = (ω l).1 ∧
        (ω' l).2.2.2 = (ω l).2.2.2 := by
      intro l
      constructor
      · change (ω l).1 = (ω l).1
        rfl
      · funext K
        change (ω l).2.2.2 K = (ω l).2.2.2 K
        rfl
    simpa [Esel, ω', split, splitFrom] using (L.elig_preActivation H ω' ω hpre)
  have hSize := hL.size_failure H hH
  let globalLegal : X.CΩ L.ht → Prop := fun ω =>
    L.ht.hp.Legal (X.pos ω) (L.elig H ω) (X.sites L.ht)
  let bad : X.CΩ L.ht → Prop := fun ω =>
    ¬ globalLegal ω ∨ ∃ a ∈ evenNbrs y, mismatch ω a
  have hMismatchBound : ∀ a : EvenRole5 n,
      (X.centreLaw L.ht H).pr (fun ω => globalLegal ω ∧ mismatch ω a) ≤
        Real.exp (-3 * (X.p.m n : ℝ) ^ ((1 : ℝ) / 5)) := by
    intro a
    have hsite : siteQuery a ∈ X.sites L.ht := by
      change siteQuery a ∈ Finset.univ.image
        (fun v : EvenRole5 n => X.St.oneHot (X.St.stateOf v.1))
      have heq : X.St.oneHot (X.St.stateOf a.1) = siteQuery a := by
        dsimp [siteQuery, Setup5.HeightChoice5.hp, Setup5.siteOf] <;> rfl
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, heq⟩
    have hHeightBound := hHeight L.ht.hp (by rfl) hHpH (by rfl)
      hHpB₀ hHpB
      hnHeight hdimLo hdimHi hreg (X.sites L.ht) (siteQuery a) hsite none auxLaw Esel
    have hheightMap : productLaw.pr (fun z =>
        L.ht.hp.Legal z.1.1 (Esel z.1.1 z.1.2) (L.ht.hp.domBall
          (X.sites L.ht) (siteQuery a) L.ht.hp.Rlong) ∧ mismatchT z a) ≤
          Real.exp (-3 * (X.p.m n : ℝ) ^ ((1 : ℝ) / 5)) := by
      simpa [productLaw, mismatchT, HDParams.posLawForced, HDParams.posLaw,
        Params5.m, Setup5.HeightChoice5.hp] using hHeightBound
    have hsubset : ∀ z,
        (legalT z ∧ mismatchT z a) →
          (L.ht.hp.Legal z.1.1 (Esel z.1.1 z.1.2) (L.ht.hp.domBall
            (X.sites L.ht) (siteQuery a) L.ht.hp.Rlong) ∧ mismatchT z a) := by
      intro z hz
      refine ⟨?_, hz.2⟩
      intro v hv j
      exact hz.1 v (Finset.mem_filter.mp hv).1 j
    have hprod := FinProb.pr_mono productLaw
      (A := fun z => legalT z ∧ mismatchT z a)
      (B := fun z => L.ht.hp.Legal z.1.1 (Esel z.1.1 z.1.2)
        (L.ht.hp.domBall (X.sites L.ht) (siteQuery a) L.ht.hp.Rlong) ∧ mismatchT z a)
      hsubset
    have hpred : (fun ω => legalT (split ω) ∧ mismatchT (split ω) a) =
        (fun ω => globalLegal ω ∧ mismatch ω a) := by
      funext ω
      simp only [legalT, globalLegal, mismatch, mismatchT, split, splitTo,
        Equiv.coe_fn_mk]
      rw [hEsel ω]
    have hIndMap :
        (FinProb.map (X.centreLaw L.ht H) split).expect
            (fun z => if legalT z ∧ mismatchT z a then 1 else 0) =
          (FinProb.map (X.centreLaw L.ht H) split).pr
            (fun z => legalT z ∧ mismatchT z a) := by
      classical
      unfold FinProb.expect FinProb.pr
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hA : legalT z ∧ mismatchT z a <;> simp [hA]
    have hIndCentre :
        (X.centreLaw L.ht H).expect
            (fun ω => if legalT (split ω) ∧ mismatchT (split ω) a then 1 else 0) =
          (X.centreLaw L.ht H).pr
            (fun ω => legalT (split ω) ∧ mismatchT (split ω) a) := by
      classical
      unfold FinProb.expect FinProb.pr
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hA : legalT (split ω) ∧ mismatchT (split ω) a <;> simp [hA]
    have hmapPrHere :
        (FinProb.map (X.centreLaw L.ht H) split).pr
          (fun z => legalT z ∧ mismatchT z a) =
          (X.centreLaw L.ht H).pr
            (fun ω => legalT (split ω) ∧ mismatchT (split ω) a) := by
      classical
      calc
        _ = (FinProb.map (X.centreLaw L.ht H) split).expect
            (fun z => if legalT z ∧ mismatchT z a then 1 else 0) := hIndMap.symm
        _ = (X.centreLaw L.ht H).expect
            (fun ω => if legalT (split ω) ∧ mismatchT (split ω) a then 1 else 0) :=
          FinProb.map_expect (X.centreLaw L.ht H) split
            (fun z => if legalT z ∧ mismatchT z a then 1 else 0)
        _ = (X.centreLaw L.ht H).pr
            (fun ω => legalT (split ω) ∧ mismatchT (split ω) a) := hIndCentre
    have htransport : productLaw.pr (fun z => legalT z ∧ mismatchT z a) =
        (X.centreLaw L.ht H).pr (fun ω => globalLegal ω ∧ mismatch ω a) := by
      calc
        _ = (FinProb.map (X.centreLaw L.ht H) split).pr
            (fun z => legalT z ∧ mismatchT z a) := by rw [hsplitLaw]
        _ = _ := hmapPrHere
        _ = _ := by rw [hpred]
    calc
      _ = productLaw.pr (fun z => legalT z ∧ mismatchT z a) := htransport.symm
      _ ≤ _ := hprod.trans hheightMap
  let M : ℝ := (X.p.m n : ℝ) ^ ((1 : ℝ) / 5)
  let cap : ℝ := Real.exp (X.p.DL n)
  let P : FinProb (X.CΩ L.ht) := X.centreLaw L.ht H
  let longMean : X.CΩ L.ht → ℝ := fun ω => (N : ℝ) *
    T.rowAt L.ht.hp.Rlong H ω y (0, x)
  let shortMean : X.CΩ L.ht → ℝ := fun ω => (N : ℝ) *
    T.rowAt (L.ht.hp.Rshort (X.p.m n)) H ω y (0, x)
  have hsum : ∑ a ∈ evenNbrs y, P.pr (fun ω => globalLegal ω ∧ mismatch ω a) ≤
      (n : ℝ) * Real.exp (-3 * M) := by
    calc
      _ ≤ ∑ a ∈ evenNbrs y, Real.exp (-3 * M) := by
        apply Finset.sum_le_sum
        intro a ha
        simpa [P, M] using hMismatchBound a
      _ = ((evenNbrs y).card : ℝ) * Real.exp (-3 * M) := by simp
      _ ≤ (n : ℝ) * Real.exp (-3 * M) := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Lane_sol_s05_hist1b.evenNbrs_card_le y)
          (Real.exp_nonneg _)
  have hcover : ∀ ω, bad ω →
      (¬ globalLegal ω ∨ ∃ a ∈ evenNbrs y, globalLegal ω ∧ mismatch ω a) := by
    intro ω hb
    rcases hb with hnot | ⟨a, ha, hmis⟩
    · exact Or.inl hnot
    · by_cases hlegal : globalLegal ω
      · exact Or.inr ⟨a, ha, hlegal, hmis⟩
      · exact Or.inl hlegal
  have hsize : P.pr (fun ω => ¬ globalLegal ω) ≤ Real.exp (-Real.sqrt n) := by
    simpa [P, globalLegal] using hSize
  have hunion := Lane_sol_s05_h5l.pr_finset_union_le P (evenNbrs y)
    (fun a ω => globalLegal ω ∧ mismatch ω a)
  have hbadBound : P.pr bad ≤ Real.exp (-Real.sqrt n) +
      (n : ℝ) * Real.exp (-3 * M) := by
    calc
      _ ≤ P.pr (fun ω => ¬ globalLegal ω ∨
          ∃ a ∈ evenNbrs y, globalLegal ω ∧ mismatch ω a) :=
        FinProb.pr_mono P (A := bad)
          (B := fun ω => ¬ globalLegal ω ∨
            ∃ a ∈ evenNbrs y, globalLegal ω ∧ mismatch ω a) hcover
      _ ≤ P.pr (fun ω => ¬ globalLegal ω) +
          P.pr (fun ω => ∃ a ∈ evenNbrs y, globalLegal ω ∧ mismatch ω a) :=
        FinProb.pr_union P _ _
      _ ≤ Real.exp (-Real.sqrt n) + (n : ℝ) * Real.exp (-3 * M) := by
        exact add_le_add hsize (by simpa [P, M] using hunion.trans hsum)
  have hcapBad : cap * P.pr bad ≤ 1 := by
    calc
      _ ≤ cap * (Real.exp (-Real.sqrt n) +
          (n : ℝ) * Real.exp (-3 * M)) :=
        mul_le_mul_of_nonneg_left hbadBound (Real.exp_nonneg _)
      _ = cap * Real.exp (-Real.sqrt n) +
          cap * (n : ℝ) * Real.exp (-3 * M) := by ring
      _ ≤ 1 / 2 + 1 / 2 := by
        refine add_le_add ?_ ?_
        · simpa [cap] using hscaleN.1
        · simpa [cap, M, mul_assoc, mul_left_comm, mul_comm] using hscaleN.2
      _ = 1 := by norm_num
  have hselEq (ω : X.CΩ L.ht) (a : EvenRole5 n) (ha : a ∈ evenNbrs y)
      (hnot : ¬ mismatch ω a) :
      X.selAt (L.elig H) ω L.ht.hp.Rlong a =
        X.selAt (L.elig H) ω (L.ht.hp.Rshort (X.p.m n)) a := by
    have hh := not_ne_iff.mp hnot
    unfold Setup5.selAt
    simpa only [siteQuery_eq a] using
      selectionAtEq (X.sites L.ht) (X.pos ω) (X.act ω) (L.elig H ω)
        (Setup5.tie ω) L.ht.hp.Rlong (L.ht.hp.Rshort (X.p.m n)) (siteQuery a) hh
  letI : DecidablePred bad := fun ω => Classical.propDecidable (bad ω)
  have hpoint : ∀ ω, longMean ω ≤ shortMean ω +
      (if bad ω then cap else 0) := by
    intro ω
    by_cases hv : L.valid H ω y
    · by_cases hb : bad ω
      · have hrowcap := T.rowAt_cap L.ht.hp.Rlong H ω y (0, x)
        have hshortnonneg : 0 ≤ shortMean ω := by
          dsimp [shortMean]
          exact mul_nonneg (Nat.cast_nonneg _) (T.rowAt_nonneg _ H ω y (0, x))
        have hbadCap : (if bad ω then cap else 0) = cap := if_pos hb
        rw [hbadCap]
        dsimp [longMean, cap]
        nlinarith [hrowcap, hshortnonneg]
      · have hsel : ∀ a ∈ evenNbrs y,
            X.selAt (L.elig H) ω L.ht.hp.Rlong a =
              X.selAt (L.elig H) ω (L.ht.hp.Rshort (X.p.m n)) a := by
          intro a ha
          exact hselEq ω a ha (by
            intro hmis
            exact hb (Or.inr ⟨a, ha, hmis⟩))
        have hrow := T.rowAt_congr L.ht.hp.Rlong
          (L.ht.hp.Rshort (X.p.m n)) H ω y hsel
        simp [longMean, shortMean, cap, hb, hrow]
    · have hzero := T.long_invalid H ω y (0, x) hv
      have hshortnonneg : 0 ≤ shortMean ω := by
        dsimp [shortMean]
        exact mul_nonneg (Nat.cast_nonneg _) (T.rowAt_nonneg _ H ω y (0, x))
      have hind : 0 ≤ (if bad ω then cap else 0) := by
        split_ifs <;> positivity
      change longMean ω ≤ shortMean ω + (if bad ω then cap else 0)
      simp only [longMean, hzero, mul_zero]
      exact add_nonneg hshortnonneg hind
  have hbonus : P.expect (fun ω => if bad ω then cap else 0) = cap * P.pr bad := by
    classical
    have hindicator : P.expect (fun ω => if bad ω then 1 else 0) = P.pr bad := by
      simp [FinProb.expect, FinProb.pr]
    calc
      P.expect (fun ω => if bad ω then cap else 0) =
          cap * P.expect (fun ω => if bad ω then 1 else 0) := by
        simp only [FinProb.expect]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hb : bad ω <;> simp [hb] <;> ring
      _ = cap * P.pr bad := congrArg (fun q : ℝ => cap * q) hindicator
  have hmean := FinProb.expect_mono P hpoint
  calc
    (X.centreLaw L.ht H).expect longMean ≤
        (X.centreLaw L.ht H).expect shortMean + 1 := by
      calc
        P.expect longMean ≤ P.expect (fun ω => shortMean ω +
            (if bad ω then cap else 0)) := hmean
        _ = P.expect shortMean + P.expect (fun ω => if bad ω then cap else 0) :=
          FinProb.expect_add P shortMean (fun ω => if bad ω then cap else 0)
        _ = P.expect shortMean + cap * P.pr bad := by rw [hbonus]
        _ ≤ P.expect shortMean + 1 := by nlinarith [hcapBad]
    _ = _ := rfl

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
