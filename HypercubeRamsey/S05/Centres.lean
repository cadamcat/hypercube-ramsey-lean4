import HypercubeRamsey.S05.History
import HypercubeRamsey.S05.Selection
import HypercubeRamsey.S03.Height.Selection

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

/-- The height exponents, chosen after `α` (05:318–325): admissible for D3.8 with `λ = n^{10}`, `D = 8`,
linear radius `r = ⌊ρ n⌋`, `θ > .9` and `2 n^b ≤ T`. -/
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
  let K := X.g.evenType (X.p.J n) v.1
  match K.2.2 with
  | some _ => Finset.univ.filter fun i => (i : ℕ) < X.p.typeBlocks n K
  | none =>
    let hits : Finset (Fin X.blockBound) :=
      match X.g.optionalKey (X.p.J n) v.1 with
      | some (.inl k) => X.hitSet (arraysOf ω) (l, K) (X.lowCol H.2 k)
      | _ => X.poolIdx
    X.firstK (if X.p.usedBlocks n ≤ hits.card then hits else X.poolIdx) (X.p.usedBlocks n)

/-- A center reference: location and block subset. -/
abbrev CRef (h : X.HeightChoice5) := h.hp.Loc × Finset (Fin X.blockBound)

/-- The reference selected at an even role by the long rule. -/
def evenRefOf (elig : X.CΩ h → h.hp.EligMap) (H : X.KeyHist) (ω : X.CΩ h) (v : EvenRole5 n) :
    Option (X.CRef h) :=
  (X.selLong elig ω v).map fun l => (l, X.refSubset H ω v l)

/-- The actual record of an odd role (05:331–343): its neighbours' selected arrays, the needed same-mode
references, and at a low role with a high neighbour, that pool and the mask hit by the actual target. -/
def actualRecord (elig : X.CΩ h → h.hp.EligMap) (H : X.KeyHist) (ω : X.CΩ h) (y : OddRole5 n) :
    X.RecordOn h.hp.Loc :=
  let ℓ := X.g.roleKey (X.p.J n) y.1
  let obs : Finset (h.hp.Loc × X.Ty) := (evenNbrs y).biUnion fun a =>
    match X.selLong elig ω a with
    | some l => {(l, X.g.evenType (X.p.J n) a.1)}
    | none => ∅
  let refs : Finset (h.hp.Loc × X.Ty × Finset (Fin X.blockBound)) := (evenNbrs y).biUnion fun a =>
    match X.selLong elig ω a with
    | some l =>
      if ℓ ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          ℓ.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome then
        {(l, X.g.evenType (X.p.J n) a.1, X.refSubset H ω a l)} else ∅
    | none => ∅
  let mask : Option (h.hp.Loc × X.Ty × Finset (Fin X.blockBound)) :=
    match ℓ with
    | .inl k =>
      if hex : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (X.selLong elig ω a).isSome then
        let a := Classical.choose hex
        match X.selLong elig ω a with
        | some l =>
          some (l, X.g.evenType (X.p.J n) a.1,
            X.firstK (X.hitSet (arraysOf ω) (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k))
              (X.p.usedBlocks n))
        | none => none
      else none
    | .inr _ => none
  (ℓ, obs, refs, mask)

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
`success` is the global geometry event of 05:835–860.  Local validity reads the center data within ambient
radius `r + slack`, `slack = o(n)`. -/
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

/-- L5.1j (05:818–894): at every good key history the marking and singleton rules, the long height rule and
uniform ties give geometry success with probability `1 - o(1)` — balls hold `λ/2..2λ` prospective centers,
maximal families of disjoint Step 3 failures have fewer than `n` members (disjoint ID sets read independent
arrays; the history bounds and the record counts), eligible sets keep `λ/3` centers, neighbouring even states
use two consecutive levels and at most `2n^b ≤ T` IDs, and every actual mapping passes Step 3 by maximality. -/
theorem L5_1j : ∀ (C : ℝ) (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        X.RecordCount C → ∃ L : X.CentreLayer5, ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
          (X.centreLaw L.ht H).pr (fun ω => ¬ L.success H ω) ≤ 1 / 100 := by
  sorry

/-! ### High rows: the common law of L5.1g (05:472–605) -/

/-- The high-row model at a feasible high record: a single datum, the next-coordinate conditionals as source,
the smoothed deletion conditionals, lengths `k_c`, cap `D_H` and cost bound `a₄`. -/
def highModel {Id : Type} [DecidableEq Id] (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (hc : X.HighCapped H r a) (hpf : X.HighPriceFeasible H r a) :
    HighRowModel5 Unit {c // c ∈ r.2.2.1} (colLen5 (X.p.s n) r.1) N where
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
  cost : ∀ H r a hc hpf, ∀ c ∈ r.2.2.1, ∑ h, ∑ y, (law H r a hc hpf).w (h, y) *
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
    ∀ c ∈ (X.actualRecord (L.elig H) H ω y).2.2.1,
      ∑ o, row H ω y o * X.highCost H (X.actualRecord (L.elig H) H ω y) (arraysOf ω) c (row H ω y) o ≤
        X.p.a 4 * (X.refLen c.2.1 c.2.2 : ℝ)
  row_local : ∀ H y, FinProb.DependsOn (fun ω => row H ω y) (X.scopeBall (h := L.ht) y.1 (L.ht.hp.r + L.slack))

/-- L5.1g, row construction (05:592–605): given a choice of common laws with the conclusions of L5.1g, the high
rows are that law at the actual record of each valid high role — feasible there by the high Step 3 test in local
validity, the true-target gate holding at a good key history. -/
theorem L5_1g_rows : ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G)
    (L : X.CentreLayer5), (∀ x : CubeVertex n, ∀ ℓ ∈ X.g.typeKeys (X.p.J n) x, (X.g.key x).1 ∈ binList5 ℓ.coarse) →
    X.HighChoice5 L.ht.hp.Loc → Nonempty (X.HighRows5 L) := by
  sorry

/-! ### Low rows: the selection adjustment of L5.1k (05:896–1001) -/

/-- The low rows (05:896–1001).  `row` is the long-rule row, `proxy` its short-rule proxy mean
`p̄^{pr}_b(y;H)`.  For every fixed base, high history and low role, `selExp` is the finite target/presentation
experiment of the selection table, with prior `π_ℓ`, whose mean identity integrates the target prior and the
raw centers. -/
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
    ∀ c ∈ (X.actualRecord (L.elig H) H ω y).2.2.1, ∀ o,
      row H ω y o ≤ Real.exp (X.p.a 4 * X.refLen c.2.1 c.2.2) *
        X.step3PostOn H (X.actualRecord (L.elig H) H ω y) (arraysOf ω) (some c) (fun _ => o.2)
  row_local : ∀ H y, FinProb.DependsOn (fun ω => row H ω y) (X.scopeBall (h := L.ht) y.1 (L.ht.hp.r + L.slack))
  long_vs_proxy : ∀ H, X.KeyGood5 H cL cH → ∀ y x, X.g.low (X.p.J n) y.1 →
    (X.centreLaw L.ht H).expect (fun ω => (N : ℝ) * row H ω y (0, x)) ≤ proxy H y x + 1
  proxy_nonneg : ∀ H y x, 0 ≤ proxy H y x
  proxy_high : ∀ H y x, ¬ X.g.low (X.p.J n) y.1 → proxy H y x = 0
  proxy_cap : ∀ H y x, proxy H y x ≤ Real.exp (X.p.DL n)
  proxy_local : ∃ Cloc : ℕ, ∀ b hi y, FinProb.DependsOn (fun lo => proxy (b, X.joinHidden hi lo) y)
    (Finset.univ.filter fun k : X.LowIdx => hammingDist k.2.1 (X.g.sign y.1) ≤ Cloc * Nat.sqrt (X.p.m n))
  Data : X.Base → X.HighHid → OddRole5 n → Type
  dataFintype : ∀ b hi y, Fintype (Data b hi y)
  selExp : ∀ b hi y, @SelectionExperiment5 (Fin N) (Data b hi y) _ (dataFintype b hi y)
  selExp_prior : ∀ b hi y, X.g.low (X.p.J n) y.1 →
    (selExp b hi y).prior = X.prior b (X.g.roleKey (X.p.J n) y.1)
  selExp_records : ∀ b hi y, Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1))) *
    (selExp b hi y).recordBound ≤ 1
  selExp_mean : ∀ b hi y lo x, X.g.low (X.p.J n) y.1 →
    ∑ y', (X.prior b (X.g.roleKey (X.p.J n) y.1)).w y' *
        proxy (b, X.joinHidden hi (Function.update lo (X.lowIdxOf (X.g.roleKey (X.p.J n) y.1))
          (fun _ => y'))) y x =
      (N : ℝ) * @Finset.sum (Data b hi y) ℝ _ (@Finset.univ _ (dataFintype b hi y)) (fun d =>
        (selExp b hi y).selectedMass d *
          (selExp b hi y).proxyRow (Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1)))) d x)

attribute [instance] LowRows5.dataFintype

/-- L5.1k, row construction (05:896–1001): the canonical records, the short-rule presentation table `a_y` (a
ratio of finite sums in the experiment with the target replaced and the unrecorded arrays regenerated at the
candidate value), the adjusted or fallback rows, the proxy means, their locality (sign distance `O(√m)`), the
long/short comparison (`o(e^{-2m^{1/5}})` mismatch at each of `O(n)` neighbouring states, cap `e^{D_L}`), and the
deletion bound `e^{a₄ k_c}` from the Step 3 bounds and the reserved selection multiplier. -/
theorem L5_1k_rows : ∀ (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
      X.p = p → (∀ x : CubeVertex n, ∀ ℓ ∈ X.g.typeKeys (X.p.J n) x, (X.g.key x).1 ∈ binList5 ℓ.coarse) →
        ∀ L : X.CentreLayer5, Nonempty (X.LowRows5 L (cL p.pre1) (cH p.pre1)) := by
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
  sorry

end Setup5

end

end HypercubeRamsey
