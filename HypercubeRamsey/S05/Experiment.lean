import HypercubeRamsey.S05.Geometry
import HypercubeRamsey.S05.Stages

/-!
# D5.2 and D5.4: the raw key experiment, block laws, and the Step 1–3 tests

The raw order is `V₀ → (A_w, W_w)_w → (U_ℓ)_ℓ → center arrays` (05:181–187).  A stream at a bin is a sequence of
`q₀`-label segments; a block of length `u` is `u / q₀` segments.  The hidden-column priors `π_ℓ` (05:118–130),
their prefix-deleted and prefix-replaced versions (05:192–197), the Step 2 block integrand and block laws
`P_K`, `P_{K,-ℓ}` (05:219–254), and the Step 3 target integrand at an abstract record (05:400–448) are
explicit finite formulas.  Undefined normalizations use the fixed fallback label `y₀` (05:651–659).
-/

namespace HypercubeRamsey

open Classical OAI.HypercubeRamsey

set_option synthInstance.maxSize 1024

noncomputable section

variable {γ K' χ : ℝ}

/-- Segments in the prefix `u_j` (05:126–130). -/
def Params5.uSeg (p : Params5 γ K' χ) (n j : ℕ) : ℕ :=
  ⌈p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) / p.q0⌉₊

/-- Segments in a high block `u_*` (05:155–157). -/
def Params5.uStarSeg (p : Params5 γ K' χ) (n : ℕ) : ℕ :=
  ⌈p.eta * Real.log (p.m n : ℝ) / p.q0⌉₊

/-- Stream length in segments: every observed prefix `b_j = u_{j+1}` (`j ≤ J`) and `u_*` fit. -/
def Params5.streamSegs (p : Params5 γ K' χ) (n : ℕ) : ℕ :=
  max (p.uSeg n (p.J n + 1)) (p.uStarSeg n)

/-- Blocks in a low array, `k_j / u_j` (05:152–154). -/
def Params5.lowBlocks (p : Params5 γ K' χ) (n j : ℕ) : ℕ :=
  ⌈p.K2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ) + (p.m n : ℝ) ^ (1 / 50 : ℝ)) /
    ((p.q0 : ℝ) * p.uSeg n j)⌉₊

/-- Blocks in a used high tuple, `k_* / u_*` (05:155–157). -/
def Params5.usedBlocks (p : Params5 γ K' χ) (n : ℕ) : ℕ :=
  ⌈(p.m n : ℝ) ^ (1 / 200 : ℝ) / ((p.q0 : ℝ) * p.uStarSeg n)⌉₊

/-- Blocks in a full high pool, `⌈e^{K_h u_*} k_* / u_*⌉` (05:157–158). -/
def Params5.poolBlocks (p : Params5 γ K' χ) (n : ℕ) : ℕ :=
  ⌈Real.exp (p.Kh * ((p.q0 : ℝ) * p.uStarSeg n)) * p.usedBlocks n⌉₊

/-- `k'_j = min_{|l-j| ≤ 1} k_l` in labels (05:444). -/
def Params5.kPrime (p : Params5 γ K' χ) (n j : ℕ) : ℕ :=
  min (min (p.q0 * p.uSeg n j * p.lowBlocks n j) (p.q0 * p.uSeg n (j + 1) * p.lowBlocks n (j + 1)))
    (p.q0 * p.uSeg n (j - 1) * p.lowBlocks n (j - 1))

/-- Segments per block of an even type. -/
def Params5.typeSegs (p : Params5 γ K' χ) (n : ℕ) {m J : ℕ} (K : EvenType5 n m J) : ℕ :=
  match K.2.2 with
  | some j => p.uSeg n j
  | none => p.uStarSeg n

/-- Blocks per array of an even type: the low tuple, or the full high pool. -/
def Params5.typeBlocks (p : Params5 γ K' χ) (n : ℕ) {m J : ℕ} (K : EvenType5 n m J) : ℕ :=
  match K.2.2 with
  | some j => p.lowBlocks n j
  | none => p.poolBlocks n

/-- Coordinates of a hidden column: one at low keys, `s` at high keys (05:118–121). -/
def colLen5 {n m J : ℕ} (s : ℕ) : HiddenKey5 n m J → ℕ
  | .inl _ => 1
  | .inr _ => s

/-- Zero-safe ratio of likelihoods. -/
def ratio5 (a b : ℝ) : ℝ := if b = 0 then 0 else a / b

/-- Normalize a weight function, with a fixed fallback point when the total mass is zero. -/
def normalize5 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (f : Ω → ℝ) (ω₀ : Ω) : FinProb Ω :=
  if h : 0 < ∑ ω, max 0 (f ω) then
    { w := fun ω => max 0 (f ω) / ∑ ω', max 0 (f ω')
      nonneg := fun ω => div_nonneg (le_max_left _ _) h.le
      sum_eq_one := by rw [← Finset.sum_div]; exact div_self h.ne' }
  else
    { w := fun ω => if ω = ω₀ then 1 else 0
      nonneg := fun ω => by split_ifs <;> norm_num
      sum_eq_one := by simp }

/-- The inputs of the construction at one dimension: constants (D5.1), the parent and stream laws (L5.1a, with
the bin-free partner law and related partners), the chunk layout (L5.1b), the state quotient (L5.1e0), and the
fixed fallback label (05:651–659). -/
structure Setup5 (γ K' χ : ℝ) (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) where
  p : Params5 γ K' χ
  P : ParentSelection5 N (BinVector5 n) χ
  S : StreamSegments5 n N p.q0 E G γ K' (p.a 0)
  g : ChunkGeometry5 n (p.m n)
  St : CubeStates5 g (p.J n)
  y₀ : Fin N
  partner_bin_free : ∀ v w w', P.prior.partner v w = P.prior.partner v w'
  partner_related : ∀ v ∈ P.lab0, ∀ w a, a ∈ P.prior.partnerSet v w → S.paired v a

namespace Setup5

variable {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} (X : Setup5 γ K' χ n N E G)

/-- Hidden keys at this dimension. -/
abbrev Key := HiddenKey5 n (X.p.m n) (X.p.J n)

/-- Even types at this dimension. -/
abbrev Ty := EvenType5 n (X.p.m n) (X.p.J n)

/-- A stream at one bin. -/
abbrev Stream := Fin (X.p.streamSegs n) → Word5 N X.p.q0

/-- Coarse base data `(A, W)` at every bin. -/
abbrev Coarse := (BinVector5 n → Fin N) × (BinVector5 n → X.Stream)

/-- Base data `(V₀, A, W)`. -/
abbrev Base := Fin N × X.Coarse

/-- Values of all hidden columns. -/
abbrev Hidden := ∀ ℓ : X.Key, Fin (colLen5 (X.p.s n) ℓ) → Fin N

/-- A key history: base data and hidden columns. -/
abbrev KeyHist := X.Base × X.Hidden

/-- A block of an even type: `u / q₀` segments. -/
abbrev Block (K : X.Ty) := Fin (X.p.typeSegs n K) → Word5 N X.p.q0

/-- An array of an even type: its blocks. -/
abbrev Array (K : X.Ty) := Fin (X.p.typeBlocks n K) → X.Block K

/-- Segment law given the two parents; on a non-related pair it is the reference law (such pairs have zero
prior weight in every posterior below). -/
def segLaw (v a : Fin N) : FinProb (Word5 N X.p.q0) :=
  if X.S.paired v a then X.S.segment v a else X.S.reference

/-- D5.2 (05:40–79): `V₀` from the parent prior, `A_w` independently from the partner law, and `W_w` as
independent segments given both parents. -/
def coarseLaw (v : Fin N) : FinProb X.Coarse :=
  FinProb.bind (FinProb.pi fun w => X.P.prior.partner v w) fun A =>
    FinProb.pi fun w => FinProb.pi fun _ : Fin (X.p.streamSegs n) => X.segLaw v (A w)

/-- The raw base law. -/
def baseLaw : FinProb X.Base := FinProb.bind X.P.prior.parent X.coarseLaw

/-- Unnormalized posterior weight of key `ℓ` at candidate `y`, with stream data `W` and only the segments
satisfying `keep` observed (05:122–130).  Interior keys: law of `A_w` given `V₀, W_w[1:b_j]`; boundary keys:
law of `V₀` given `(A_{w'}, W_{w'}[1:b_j])_{w' ∈ C_i}`. -/
def colWeight (b : X.Base) (ℓ : X.Key) (W : BinVector5 n → X.Stream)
    (keep : BinVector5 n → Fin (X.p.streamSegs n) → Prop) (y : Fin N) : ℝ :=
  let k := X.p.uSeg n (ℓ.level + 1)
  let lik : Fin N → Fin N → BinVector5 n → ℝ := fun v a w =>
    ∏ s : Fin (X.p.streamSegs n), if (s : ℕ) < k ∧ keep w s then (X.segLaw v a).w (W w s) else 1
  if ℓ.coarse.2 then
    X.P.prior.parent.w y *
      ∏ w' ∈ binList5 ℓ.coarse, ((X.P.prior.partner y w').w (b.2.1 w') * lik y (b.2.1 w') w')
  else (X.P.prior.partner b.1 ℓ.coarse.1).w y * lik b.1 y ℓ.coarse.1

/-- The hidden-column prior `π_ℓ` at base data `b`. -/
def prior (b : X.Base) (ℓ : X.Key) : Law N :=
  normalize5 (X.colWeight b ℓ b.2.2 fun _ _ => True) X.y₀

/-- `π_{ℓ,-w,k}`: the observation `W_w[1:k]` (in segments) removed (05:194–197). -/
def priorDel (b : X.Base) (ℓ : X.Key) (w : BinVector5 n) (k : ℕ) : Law N :=
  normalize5 (X.colWeight b ℓ b.2.2 fun w' s => ¬ (w' = w ∧ (s : ℕ) < k)) X.y₀

/-- Replace the first `k` segments of the stream at bin `w`. -/
def replaceStream (W : BinVector5 n → X.Stream) (w : BinVector5 n) {k : ℕ}
    (z : Fin k → Word5 N X.p.q0) : BinVector5 n → X.Stream :=
  Function.update W w fun s => if h : (s : ℕ) < k then z ⟨s, h⟩ else W w s

/-- `π_ℓ` with the block `W_w[1:k]` replaced by `z`. -/
def priorRep (b : X.Base) (ℓ : X.Key) (w : BinVector5 n) {k : ℕ}
    (z : Fin k → Word5 N X.p.q0) : Law N :=
  normalize5 (X.colWeight b ℓ (X.replaceStream b.2.2 w z) fun _ _ => True) X.y₀

/-- The hidden columns are independent given the base, each coordinate with law `π_ℓ` (05:118–121). -/
def hiddenLaw (b : X.Base) : FinProb X.Hidden :=
  FinProb.pi fun ℓ => FinProb.pi fun _ => X.prior b ℓ

/-- The raw law of key histories. -/
def keyLaw : FinProb X.KeyHist := FinProb.bind X.baseLaw X.hiddenLaw

/-- The raw law of the coarse base and hidden columns given `V₀ = v`. -/
def keyLawAt (v : Fin N) : FinProb (X.Coarse × X.Hidden) :=
  FinProb.bind (X.coarseLaw v) fun c => X.hiddenLaw (v, c)

/-- The keys whose Step 1 comparisons enter the block gate of a type: its list `S`, and at a high type the
potentially used optional key (05:222–226; the prior does not depend on the sign). -/
def gateKeys (K : X.Ty) : Finset X.Key :=
  K.2.1 ∪ if K.2.2 = none then {.inl (K.1, fun _ => false, ⟨X.p.J n, Nat.lt_succ_self _⟩)} else ∅

/-- The true-parent segment law of a block, `P₀` (05:221). -/
def blockBase (b : X.Base) (K : X.Ty) (z : X.Block K) : ℝ :=
  ∏ s, (X.segLaw b.1 (b.2.1 K.1.1)).w (z s)

/-- `L_ℓ(z; θ)`: likelihood of `U_ℓ = θ` with the base block replaced by `z`, relative to `π_{ℓ,-w,u}^{⊗ s_ℓ}`
(05:228–233). -/
def colLik (b : X.Base) (K : X.Ty) (ℓ : X.Key) (z : X.Block K)
    (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) : ℝ :=
  ∏ h, ratio5 ((X.priorRep b ℓ K.1.1 z).w (θ h)) ((X.priorDel b ℓ K.1.1 (X.p.typeSegs n K)).w (θ h))

/-- The Step 2 gate `𝒢_K`: the Step 1 comparisons at the block hold for every gate key (05:222–226). -/
def blockGate (b : X.Base) (K : X.Ty) (z : X.Block K) : Prop :=
  ∀ ℓ ∈ X.gateKeys K, ∀ y, (X.priorRep b ℓ K.1.1 z).w y ≤
    Real.exp (X.p.a 1 * (X.p.q0 * X.p.typeSegs n K)) *
      (X.priorDel b ℓ K.1.1 (X.p.typeSegs n K)).w y

/-- The Step 2 integrand over the listed keys `keys` (05:234–238). -/
def blockWeight (H : X.KeyHist) (K : X.Ty) (keys : Finset X.Key) (z : X.Block K) : ℝ :=
  X.blockBase H.1 K z * (if X.blockGate H.1 K z then 1 else 0) *
    ∏ ℓ ∈ keys, X.colLik H.1 K ℓ z (H.2 ℓ)

/-- `m_S` (05:234–238). -/
def blockMass (H : X.KeyHist) (K : X.Ty) (keys : Finset X.Key) : ℝ :=
  ∑ z, X.blockWeight H K keys z

/-- The constant fallback block. -/
def fallbackBlock (K : X.Ty) : X.Block K := fun _ _ => X.y₀

/-- `P_K` normalized over the listed keys (05:239–241). -/
def blockLawOn (H : X.KeyHist) (K : X.Ty) (keys : Finset X.Key) : FinProb (X.Block K) :=
  normalize5 (X.blockWeight H K keys) (X.fallbackBlock K)

/-- `P_K` at a key history. -/
def blockLaw (H : X.KeyHist) (K : X.Ty) : FinProb (X.Block K) := X.blockLawOn H K K.2.1

/-- `P_{K,-ℓ}`. -/
def blockLawDel (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key) : FinProb (X.Block K) :=
  X.blockLawOn H K (K.2.1.erase ℓ)

/-- A key history with one hidden column replaced (05:186–187: later kernels are evaluated at the new value). -/
def withCol (H : X.KeyHist) (ℓ : X.Key) (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) : X.KeyHist :=
  (H.1, Function.update H.2 ℓ θ)

/-- The value of a low hidden column (a single coordinate). -/
def lowCol (U : X.Hidden) (k : CoarseKey5 n × CubeVertex (X.p.m n) × Fin (X.p.J n + 1)) : Fin N :=
  U (.inl k) ⟨0, by simp [colLen5]⟩

/-- The true block `W_w[1:u]` of a type at base `b`. -/
def trueBlock (b : X.Base) (K : X.Ty) : X.Block K := fun s =>
  if h : (s : ℕ) < X.p.streamSegs n then b.2.2 K.1.1 ⟨s, h⟩ else fun _ => X.y₀

/-! ### Occurring roles, types and keys -/

/-- An even type that occurs at some even role. -/
def TypeOccurs (K : X.Ty) : Prop := ∃ x : CubeVertex n, IsEvenRole x ∧ X.g.evenType (X.p.J n) x = K

/-- A key that is the key of some odd role or appears in an occurring gate list. -/
def KeyOccurs (ℓ : X.Key) : Prop :=
  (∃ y : CubeVertex n, ¬ IsEvenRole y ∧ X.g.roleKey (X.p.J n) y = ℓ) ∨
    ∃ K, X.TypeOccurs K ∧ ℓ ∈ X.gateKeys K

/-- The optional key `(i, t, J)` of a high type at sign `t`. -/
def optKeyOf (K : X.Ty) (t : CubeVertex (X.p.m n)) : X.Key :=
  .inl (K.1, t, ⟨X.p.J n, Nat.lt_succ_self _⟩)

/-- An optional (type, sign) pair: some high even role with `j = J + 1` has this type and sign. -/
def OptOccurs (K : X.Ty) (t : CubeVertex (X.p.m n)) : Prop :=
  ∃ x : CubeVertex n, IsEvenRole x ∧ X.g.evenType (X.p.J n) x = K ∧
    X.g.optionalKey (X.p.J n) x = some (X.optKeyOf K t)

/-! ### Step 1 and Step 2 tests -/

/-- Step 1 comparison failure for key `ℓ` and the prefix `W_w[1:k]` (05:199–206). -/
def step1Fail (b : X.Base) (ℓ : X.Key) (w : BinVector5 n) (k : ℕ) : Prop :=
  ∃ y, Real.exp (X.p.a 1 * (X.p.q0 * k)) * (X.priorDel b ℓ w k).w y < (X.prior b ℓ).w y

/-- Step 1 prior-cap failure `N max π_ℓ > exp(K' b_j)` (05:207–211). -/
def capFail (b : X.Base) (ℓ : X.Key) : Prop :=
  ∃ y, Real.exp (X.p.Kcap * (X.p.q0 * X.p.uSeg n (ℓ.level + 1))) < (N : ℝ) * (X.prior b ℓ).w y

/-- All listed Step 1 tests pass at the base. -/
def Step1Pass (b : X.Base) : Prop :=
  (∀ K, X.TypeOccurs K → ∀ ℓ ∈ X.gateKeys K, ¬ X.step1Fail b ℓ K.1.1 (X.p.typeSegs n K)) ∧
    ∀ ℓ, X.KeyOccurs ℓ → ¬ X.capFail b ℓ

/-- A Step 2 failure at a type: a failed denominator test intersected with the true-block gate (05:242–248,
05:617–619). -/
def step2Fail (H : X.KeyHist) (K : X.Ty) : Prop :=
  X.blockGate H.1 K (X.trueBlock H.1 K) ∧
    (X.blockMass H K K.2.1 <
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) * ∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ)) ∨
      ∃ ℓ ∈ K.2.1, X.blockMass H K K.2.1 <
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) * colLen5 (X.p.s n) ℓ) *
          X.blockMass H K (K.2.1.erase ℓ))

/-- The optional small-prefix test `m_{S+ℓ}/m_S ≥ e^{-δ u_*}` at a high type (05:256–259). -/
def optFail (H : X.KeyHist) (K : X.Ty) (t : CubeVertex (X.p.m n)) : Prop :=
  X.blockGate H.1 K (X.trueBlock H.1 K) ∧
    X.blockMass H K (insert (X.optKeyOf K t) K.2.1) <
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n))) * X.blockMass H K K.2.1

/-- All occurring Step 2 tests pass at the key history. -/
def Step2Pass (H : X.KeyHist) : Prop :=
  (∀ K, X.TypeOccurs K → ¬ X.step2Fail H K) ∧ ∀ K t, X.OptOccurs K t → ¬ X.optFail H K t

/-! ### Step 3 records (05:331–470)

Records are generic in the type of center IDs: abstract records use IDs renamed into `[T]` (history tests),
actual records use the ambient locations of the height device. -/

/-- Number of block indices used by records: an upper bound for every array. -/
def blockBound : ℕ := max (X.p.poolBlocks n) (Finset.univ.sup fun j : Fin (X.p.J n + 1) => X.p.lowBlocks n j)

/-- The first `k` elements of a set of block indices (05:158–160: the used tuple is formed from the first
`k_* / u_*` blocks with the required hits). -/
def firstK (S : Finset (Fin X.blockBound)) (k : ℕ) : Finset (Fin X.blockBound) :=
  S.filter fun i => (S.filter fun i' => i' < i).card < k

/-- Block indices of a full high pool. -/
def poolIdx : Finset (Fin X.blockBound) := Finset.univ.filter fun i => (i : ℕ) < X.p.poolBlocks n

/-- A record over IDs `Id` (05:331–343, 05:476–479): target key, the distinct observed (ID, type) arrays, the
needed same-mode references (observed arrays with block subsets), and at a low record with a high pool, that
pool and its mask. -/
abbrev RecordOn (Id : Type) := X.Key × Finset (Id × X.Ty) ×
  Finset (Id × X.Ty × Finset (Fin X.blockBound)) × Option (Id × X.Ty × Finset (Fin X.blockBound))

/-- Arrays at every (ID, type). -/
abbrev ArraysOn (Id : Type) := ∀ c : Id × X.Ty, X.Array c.2

/-- Whether a block index is inside an array of type `K`. -/
def blockIdx (K : X.Ty) (i : Fin X.blockBound) : Option (Fin (X.p.typeBlocks n K)) :=
  if h : (i : ℕ) < X.p.typeBlocks n K then some ⟨i, h⟩ else none

/-- Every entry of a block hits the column `y`. -/
def BlockHits (K : X.Ty) (z : X.Block K) (y : Fin N) : Prop := ∀ s i, Hits E G (z s i) y

/-- The pool blocks all of whose entries hit the column `y`. -/
def hitSet {Id : Type} (a : X.ArraysOn Id) (c : Id × X.Ty) (y : Fin N) : Finset (Fin X.blockBound) :=
  X.poolIdx.filter fun i => ∃ i', X.blockIdx c.2 i = some i' ∧ X.BlockHits c.2 (a c i') y

/-- The candidate gate `Θ(ϑ)` (05:419–428): positive `m_{S-ℓ}` and the Step 2 lower ratio at every observed type
containing the target, and at a low record with a high pool, that the candidate selects exactly the specified
successful mask (the first `k_* / u_*` hitting blocks). -/
def candGateOn {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) : Prop :=
  (∀ c ∈ r.2.1, r.1 ∈ c.2.2.1 →
    0 < X.blockMass H c.2 (c.2.2.1.erase r.1) ∧
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n c.2)) * colLen5 (X.p.s n) r.1) *
          X.blockMass H c.2 (c.2.2.1.erase r.1) ≤ X.blockMass (X.withCol H r.1 θ) c.2 c.2.2.1) ∧
    ∀ c M, r.2.2.2 = some (c.1, c.2, M) →
      ∀ h, X.p.usedBlocks n ≤ (X.hitSet a c (θ h)).card ∧
        X.firstK (X.hitSet a c (θ h)) (X.p.usedBlocks n) = M

/-- Whether block `i` of array `c` belongs to the reference `excl`. -/
def InRef {Id : Type} (excl : Option (Id × X.Ty × Finset (Fin X.blockBound))) (c : Id × X.Ty)
    (i : Fin (X.p.typeBlocks n c.2)) : Prop :=
  ∃ e, excl = some e ∧ c = (e.1, e.2.1) ∧ ∃ j ∈ e.2.2, X.blockIdx c.2 j = some i

/-- The likelihood of the observed blocks given target value `θ`, relative to `P_{K,-ℓ}` (05:415–418), with the
blocks of the deleted reference `excl` removed. -/
def obsLikOn {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N)
    (excl : Option (Id × X.Ty × Finset (Fin X.blockBound))) : ℝ :=
  ∏ c ∈ r.2.1.filter (fun c => r.1 ∈ c.2.2.1), ∏ i : Fin (X.p.typeBlocks n c.2),
    if X.InRef excl c i then 1
    else ratio5 ((X.blockLaw (X.withCol H r.1 θ) c.2).w (a c i)) ((X.blockLawDel H c.2 r.1).w (a c i))

/-- The Step 3 integrand `M` (`excl = none`) and `M_{-c}` (05:429–434). -/
def step3MassOn {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (excl : Option (Id × X.Ty × Finset (Fin X.blockBound))) : ℝ :=
  ∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
    (∏ h, (X.prior H.1 r.1).w (θ h)) * (if X.candGateOn H r a θ then 1 else 0) * X.obsLikOn H r a θ excl

/-- The Step 3 posterior `𝒫` (`excl = none`) and the deleted posterior `𝒬_c` (05:455–458). -/
def step3PostOn {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (excl : Option (Id × X.Ty × Finset (Fin X.blockBound)))
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) : ℝ :=
  (∏ h, (X.prior H.1 r.1).w (θ h)) * (if X.candGateOn H r a θ then 1 else 0) *
    X.obsLikOn H r a θ excl / X.step3MassOn H r a excl

/-- Length `k_c` of a reference, in labels. -/
def refLen (K : X.Ty) (M : Finset (Fin X.blockBound)) : ℕ :=
  M.card * (X.p.q0 * X.p.typeSegs n K)

/-! #### High rows: next-coordinate conditionals and feasibility (05:472–605) -/

/-- Conditional law of coordinate `h` given the prefix of `θ`, under path weights `P`. -/
def condCoord {s : ℕ} (P : (Fin s → Fin N) → ℝ) (θ : Fin s → Fin N) (h : Fin s) : Law N :=
  normalize5 (fun y => ∑ ϑ : Fin s → Fin N,
    if (∀ h' : Fin s, h' < h → ϑ h' = θ h') ∧ ϑ h = y then P ϑ else 0) X.y₀

/-- Smoothing with a fixed uniform component (`1/2`) (05:487–489). -/
def smooth (Q : Law N) : Law N where
  w y := (Q.w y + (N : ℝ)⁻¹) / 2
  nonneg y := by have := Q.nonneg y; positivity
  sum_eq_one := by
    have hN : (N : ℝ) ≠ 0 := by
      have : 0 < N := Fin.pos X.y₀
      exact_mod_cast this.ne'
    rw [← Finset.sum_div, Finset.sum_add_distrib, Q.sum_eq_one]
    simp [Finset.card_univ, Fintype.card_fin, hN]

/-- The high-row data at a high record (05:483–490): next-coordinate conditionals `𝒫_h` of the posterior along
the true prefix, and smoothed deletion conditionals `𝒬̃_{c,h}` for every needed reference. -/
def highSource {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id) (h : Fin (colLen5 (X.p.s n) r.1)) :
    Law N :=
  X.condCoord (X.step3PostOn H r a none) (H.2 r.1) h

/-- Smoothed deletion conditional of a reference. -/
def highDeleted {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (h : Fin (colLen5 (X.p.s n) r.1)) : Law N :=
  X.smooth (X.condCoord (X.step3PostOn H r a (some c)) (H.2 r.1) h)

/-- The capped, supported laws on index–label pairs exist (05:557–573). -/
def HighCapped {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id) : Prop :=
  ∃ R : FinProb (Fin (colLen5 (X.p.s n) r.1) × Fin N),
    (∀ h y, R.w (h, y) ≤ 2 * Real.exp (X.p.DH n) / ((colLen5 (X.p.s n) r.1 : ℝ) * N)) ∧
    (∀ h y, R.w (h, y) ≠ 0 → (X.highSource H r a h).w y ≠ 0)

/-- Price feasibility of all deletion costs (05:574–580): for every price on the needed references, some capped,
supported law has weighted cost at most the weighted bound `a₄ k_c`. -/
def HighPriceFeasible {Id : Type} [DecidableEq Id] (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id) : Prop :=
  ∀ price : {c // c ∈ r.2.2.1} → ℝ, (∀ c, 0 ≤ price c) → (∑ c, price c = 1) →
    ∃ R : FinProb (Fin (colLen5 (X.p.s n) r.1) × Fin N),
      (∀ h y, R.w (h, y) ≤ 2 * Real.exp (X.p.DH n) / ((colLen5 (X.p.s n) r.1 : ℝ) * N)) ∧
      (∀ h y, R.w (h, y) ≠ 0 → (X.highSource H r a h).w y ≠ 0) ∧
      ∑ c, price c * (∑ h, ∑ y, R.w (h, y) *
        highDeletionCost5 R (fun c' h' => X.highDeleted H r a c'.1 h') c h y) ≤
        ∑ c, price c * (X.p.a 4 * (X.refLen c.1.2.1 c.1.2.2 : ℝ))

/-- Step 3 failure at a record: a failed lower test, a failed ratio test at a needed reference, or at a high
target the failure of the high-row path tests (feasibility), intersected with the true-target gate
(05:445–453, 05:494–566, 05:619–623). -/
def step3FailOn {Id : Type} [DecidableEq Id] (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id) : Prop :=
  X.candGateOn H r a (H.2 r.1) ∧
    (X.step3MassOn H r a none <
        (match r.1 with
          | .inl k => Real.exp (-(X.p.delta * X.p.kPrime n k.2.2.val))
          | .inr _ => Real.exp (-(X.p.delta * X.p.s n))) ∨
      (∃ c ∈ r.2.2.1, X.step3MassOn H r a none <
        Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) *
          X.step3MassOn H r a (some c)) ∨
      (r.1.isRight ∧ ¬ (X.HighCapped H r a ∧ X.HighPriceFeasible H r a)))

/-- Abstract records: IDs renamed into `[T]` (05:375–378). -/
abbrev AbsRecord := X.RecordOn (Fin (X.p.T n))

/-- Fresh arrays at a key history: independent `P_K` blocks at every renamed ID and type (05:249–254). -/
def recArrayLaw (H : X.KeyHist) : FinProb (X.ArraysOn (Fin (X.p.T n))) :=
  FinProb.pi fun (c : Fin (X.p.T n) × X.Ty) => FinProb.pi fun _ => X.blockLaw H c.2

/-- The conditional Step 3 failure probability over fresh arrays at a key history (05:609–613). -/
def step3Rate (H : X.KeyHist) (r : X.AbsRecord) : ℝ :=
  (X.recArrayLaw H).pr (X.step3FailOn H r)

/-- The even neighbours of an odd role. -/
def evenNbrs (y : OddRole5 n) : Finset (EvenRole5 n) :=
  Finset.univ.filter fun a : EvenRole5 n => (cube n).Adj a.1 y.1

/-- A legitimate reference block subset of an array of type `K`: the whole low array, or `k_* / u_*` blocks
of a high pool. -/
def LegitRef (K : X.Ty) (M : Finset (Fin X.blockBound)) : Prop :=
  match K.2.2 with
  | some _ => ∀ i : Fin X.blockBound, i ∈ M ↔ (i : ℕ) < X.p.typeBlocks n K
  | none => M.card = X.p.usedBlocks n ∧ M ⊆ X.poolIdx

/-- A record over IDs `Id` arising from an odd role and an assignment of IDs to the states of its even
neighbours (05:331–343): the observed arrays are the distinct (ID, type) pairs of the neighbours, the references
are legitimate subsets of same-mode neighbours' arrays (all of them containing the target), and a mask (low
targets only) is a successful subset of a high neighbour's pool. -/
def RecordFrom {Id : Type} (r : X.RecordOn Id) (y : OddRole5 n) (μ : X.St.Site → Id) : Prop :=
  X.g.roleKey (X.p.J n) y.1 = r.1 ∧
  r.2.1 = (evenNbrs y).image (fun a => (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1)) ∧
  (∀ c ∈ r.2.2.1, ∃ a₀ ∈ evenNbrs y, c.1 = μ (X.St.stateOf a₀.1) ∧
    c.2.1 = X.g.evenType (X.p.J n) a₀.1 ∧ r.1 ∈ c.2.1.2.1 ∧
    r.1.isLeft = c.2.1.2.2.isSome ∧ X.LegitRef c.2.1 c.2.2) ∧
  (match r.2.2.2 with
    | none => True
    | some (i, K, M) => r.1.isLeft ∧ ∃ a₁ ∈ evenNbrs y, K = X.g.evenType (X.p.J n) a₁.1 ∧
        K.2.2 = none ∧ i = μ (X.St.stateOf a₁.1) ∧ M.card = X.p.usedBlocks n ∧ M ⊆ X.poolIdx)

/-- An abstract record that can occur. -/
def RecOccurs (r : X.AbsRecord) : Prop := ∃ y μ, X.RecordFrom r y μ

end Setup5

end

end HypercubeRamsey
