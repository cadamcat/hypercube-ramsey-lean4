import HypercubeRamsey.Framework.Props

/-!
# Section 8.1 finite experiment

The definitions in this file fix the finite objects used by the L8.1 nodes.  The grid uses singleton
chunk-count bins; the bin-mass and locality estimates are separate theorem fields, so this choice remains
explicitly checkable in L8.1a.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey

/-- The number of special chunks, `ceil(n^τ)`. -/
noncomputable def L81ChunkCount (n : ℕ) (η₀ : ℝ) : ℕ :=
  Nat.ceil ((n : ℝ) ^ tau8 η₀)

/-- The number of bits in each special chunk, `floor(n^.2)`. -/
noncomputable def L81ChunkLength (n : ℕ) : ℕ :=
  Nat.floor ((n : ℝ) ^ ((1 : ℝ) / 5))

/-- Number of special bits. -/
noncomputable def L81SpecialBits (n : ℕ) (η₀ : ℝ) : ℕ :=
  L81ChunkCount n η₀ * L81ChunkLength n

/-- Key grid: each chunk's Hamming weight is its singleton bin. -/
abbrev L81GridKey (n : ℕ) (η₀ : ℝ) :=
  Fin (L81ChunkCount n η₀) → Fin (L81ChunkLength n + 1)

/-- Residual cube after the special bits. -/
abbrev L81Residual (n : ℕ) (η₀ : ℝ) :=
  CubeVertex (n - L81SpecialBits n η₀)

/-- Hamming weight of a cube word. -/
noncomputable def L81WordWeight {m : ℕ} (v : CubeVertex m) : ℕ :=
  (Finset.univ.filter fun j => v j = true).card

/-- Number of true coordinates in a chunk of a full cube word. Positions beyond `n` are padded by false;
L8.1a supplies the eventual split bound that makes this padding inactive. -/
noncomputable def L81ChunkWeight (n : ℕ) (η₀ : ℝ) (v : CubeVertex n)
    (i : Fin (L81ChunkCount n η₀)) : ℕ :=
  ∑ j : Fin (L81ChunkLength n),
    if h : i.val * L81ChunkLength n + j.val < n then
      if v ⟨i.val * L81ChunkLength n + j.val, h⟩ then 1 else 0
    else 0

/-- Grid key of a cube vertex. The `min` makes this definition total even before the split bound is known. -/
noncomputable def L81KeyOf {n : ℕ} (η₀ : ℝ) (v : CubeVertex n) : L81GridKey n η₀ :=
  fun i => ⟨min (L81ChunkWeight n η₀ v i) (L81ChunkLength n),
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- Residual word of a cube vertex. -/
noncomputable def L81ResidualOf {n : ℕ} (η₀ : ℝ) (v : CubeVertex n) : L81Residual n η₀ :=
  fun j => if h : L81SpecialBits n η₀ + j.val < n then
    v ⟨L81SpecialBits n η₀ + j.val, h⟩ else false

/-- The grid/residual cell associated with a cube vertex. -/
noncomputable def L81CellOf {n : ℕ} (η₀ : ℝ) (v : CubeVertex n) :
    L81GridKey n η₀ × L81Residual n η₀ :=
  (L81KeyOf η₀ v, L81ResidualOf η₀ v)

/-- L1 distance in the key grid. -/
noncomputable def L81GridDistance {n : ℕ} {η₀ : ℝ}
    (g u : L81GridKey n η₀) : ℕ :=
  ∑ j, Nat.dist (g j).val (u j).val

/-- Hamming distance in a residual cube. -/
noncomputable def L81ResidualDistance {n : ℕ} {η₀ : ℝ}
    (a b : L81Residual n η₀) : ℕ :=
  (Finset.univ.filter fun j => a j ≠ b j).card

/-- Padded ordinary or cross adjacency of cells. -/
def L81PaddedAdjacent {n : ℕ} {η₀ : ℝ}
    (c d : L81GridKey n η₀ × L81Residual n η₀) : Prop :=
  (c.1 = d.1 ∧ L81ResidualDistance c.2 d.2 ≤ 1) ∨
  (c.2 = d.2 ∧ L81GridDistance c.1 d.1 = 1)

/-- Probability that a uniformly random chunk has the specified singleton-bin weight. -/
noncomputable def L81ChunkBinMass (n : ℕ) (b : Fin (L81ChunkLength n + 1)) : ℝ :=
  ((Finset.univ.filter fun v : CubeVertex (L81ChunkLength n) =>
    L81WordWeight v = b.val).card : ℝ) / (2 ^ L81ChunkLength n : ℝ)

/-- Probability that two independent uniform cube words have keys within grid distance eight. -/
noncomputable def L81GridNearFraction (n : ℕ) (η₀ : ℝ) : ℝ := by
  classical
  let V := CubeVertex n
  exact ((Finset.univ.product Finset.univ).filter fun z : V × V =>
    L81GridDistance (L81KeyOf η₀ z.1) (L81KeyOf η₀ z.2) ≤ 8).card /
      (Fintype.card V : ℝ) ^ 2

/-- Probability that two independent uniform residual words are within Hamming radius `R`. -/
noncomputable def L81ResidualNearFraction (n : ℕ) (η₀ : ℝ) (R : ℕ) : ℝ := by
  classical
  let Q := L81Residual n η₀
  exact ((Finset.univ.product Finset.univ).filter fun z : Q × Q =>
    L81ResidualDistance z.1 z.2 ≤ R).card / (Fintype.card Q : ℝ) ^ 2

/-- L8.1a's geometric and counting conclusions. -/
structure L81GridFacts (n : ℕ) (η₀ : ℝ) : Prop where
  split : L81SpecialBits n η₀ ≤ n
  edge_cover : ∀ v w : CubeVertex n,
    (cube n).Adj v w → L81PaddedAdjacent (L81CellOf η₀ v) (L81CellOf η₀ w)
  bin_mass : ∀ b : Fin (L81ChunkLength n + 1),
    L81ChunkBinMass n b ≤ 2 * (n : ℝ) ^ (-(0.04 : ℝ))
  grid_near : ∃ C : ℝ, 0 ≤ C ∧
    L81GridNearFraction n η₀ ≤ (n : ℝ) ^ C *
      (2 * (n : ℝ) ^ (-(0.04 : ℝ))) ^ L81ChunkCount n η₀
  residual_near : ∃ c : ℝ, 0 < c ∧
    L81ResidualNearFraction n η₀ (Nat.floor ((0.0201 : ℝ) * n)) ≤
      Real.exp (-c * n)

/-- All hypotheses consumed by L8.1 at one dimension. -/
structure L81Input (η₀ γ β p K : ℝ) (n₀ : ℕ) (C₀ : ℝ)
    (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
    (G : Colour) (M : TagMix N) : Prop where
  large : LargeAt n₀ C₀ n N
  discrepancy : DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀)
    ((n : ℝ) ^ (-η₀))
  balanced : M.Balanced K
  laws : ∀ i, 0 < M.Λ i →
    (M.μ i).SupportedIn X ∧ (M.ν i).SupportedIn Y ∧
    (M.μ i).WidthLE ((n : ℝ) ^ γ) ∧ (M.ν i).WidthLE ((n : ℝ) ^ β) ∧
    ∀ y, 0 < (M.ν i).w y →
      1 - Real.exp (-((n : ℝ) ^ p)) ≤ colDeg E G (M.μ i) y

/-- The trimmed tag mixture from L8.1b. -/
structure L81TrimmedMix {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    (I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M) (h : ℕ) where
  removed : Finset (Fin N)
  weight : M.ι → ℝ
  μ : M.ι → Law N
  ν : M.ι → Law N
  removed_subset : removed ⊆ X
  removed_card : (removed.card : ℝ) ≤ 2 * N * Real.exp (-((n : ℝ) ^
    (min (η₀ / 2) (4 / 100 : ℝ)) / 2))
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  balanced : (∀ x, (N : ℝ) * ∑ i, weight i * (μ i).w x ≤ 4 * K) ∧
    (∀ y, (N : ℝ) * ∑ i, weight i * (ν i).w y ≤ 4 * K)
  support_width_degree : ∀ i, 0 < weight i →
    (μ i).SupportedIn (X \ removed) ∧ (ν i).SupportedIn Y ∧
    (μ i).WidthLE ((n : ℝ) ^ γ + Real.log 2) ∧ (ν i).WidthLE ((n : ℝ) ^ β) ∧
    ∀ y, 0 < (ν i).w y →
      1 - 2 * Real.exp (-((n : ℝ) ^ p)) ≤ colDeg E G (μ i) y
  total_variation : (1 / 2 : ℝ) * ∑ i, |weight i - M.Λ i| ≤
    8 * K * Real.exp (-((n : ℝ) ^ (min (η₀ / 2) (4 / 100 : ℝ)) / 2))
  survival : ∀ x ∈ X \ removed,
    |(∑ i, weight i * (rowDeg E G x (ν i)) ^ h) - (2 : ℝ) ^ (-(h : ℝ))| ≤
      (2 : ℝ) ^ (-(h : ℝ)) * (n : ℝ) ^
        (-(min (η₀ / 2) (4 / 100 : ℝ)) / 2)

/-- A hidden tuple is the `h` independent second-side labels sampled at one grid key. -/
abbrev L81HiddenTuple (h N : ℕ) := Fin h → Fin N

/-- The hidden tuple prior, obtained by first sampling a trimmed tag and then `h` labels from its second law. -/
noncomputable def L81TupleLaw {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) : FinProb (L81HiddenTuple h N) := by
  classical
  let tags : FinProb M.ι :=
    { w := T.weight, nonneg := T.weight_nonneg, sum_eq_one := T.weight_sum }
  exact FinProb.map
    (FinProb.bind tags (fun i => FinProb.pi (fun _ : Fin h => T.ν i))) Prod.snd

/-- Hidden tuples, sampled independently over the key grid. -/
noncomputable def L81HiddenLaw {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) : FinProb (L81GridKey n η₀ → L81HiddenTuple h N) :=
  FinProb.pi (fun _ : L81GridKey n η₀ => L81TupleLaw T)

/-- Posterior tag mass after observing a hidden tuple. -/
noncomputable def L81PosteriorWeight {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (θ : L81HiddenTuple h N) (i : M.ι) : ℝ := by
  classical
  let numerator := T.weight i * ∏ j, (T.ν i).w (θ j)
  exact if (L81TupleLaw T).w θ = 0 then 0 else numerator / (L81TupleLaw T).w θ

/-- Hidden tuple assignments over every grid key. -/
abbrev L81HiddenHistory (n : ℕ) (η₀ : ℝ) (h N : ℕ) :=
  L81GridKey n η₀ → L81HiddenTuple h N

/-- Keys adjacent by one bin-step. -/
noncomputable def L81CrossKeys {n : ℕ} {η₀ : ℝ} (g : L81GridKey n η₀) : Finset (L81GridKey n η₀) :=
  Finset.univ.filter fun u => L81GridDistance g u = 1

/-- A tuple hits at a first-side label in the selected colour. -/
def L81HitsTuple {N h : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (x : Fin N) (θ : L81HiddenTuple h N) : Prop :=
  ∀ j, Hits E G x (θ j)

/-- Cross-neighbour hit mass before the own tuple is imposed. -/
noncomputable def L81DMinus {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (Θ : L81HiddenHistory n η₀ h N)
    (g : L81GridKey n η₀) (i : M.ι) : ℝ := by
  classical
  exact ∑ x, (T.μ i).w x * if ∀ u ∈ L81CrossKeys g, L81HitsTuple E G x (Θ u) then 1 else 0

/-- Cross-neighbour and own-key hit mass. -/
noncomputable def L81DPlus {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (Θ : L81HiddenHistory n η₀ h N)
    (g : L81GridKey n η₀) (i : M.ι) : ℝ := by
  classical
  exact ∑ x, (T.μ i).w x * if (∀ u ∈ L81CrossKeys g, L81HitsTuple E G x (Θ u)) ∧
      L81HitsTuple E G x (Θ g) then 1 else 0

/-- The independent-hit reference mass `2^{-h|E(g)|}`. -/
noncomputable def L81AG {n : ℕ} {η₀ : ℝ} (h : ℕ) (g : L81GridKey n η₀) : ℝ :=
  (2 : ℝ) ^ (-(h : ℝ) * (L81CrossKeys g).card)

/-- Add one omitted cross key back to the ordinary cross-hit condition. -/
noncomputable def L81DMinusOmit {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (Θ : L81HiddenHistory n η₀ h N)
    (g u₀ : L81GridKey n η₀) (i : M.ι) : ℝ := by
  classical
  exact ∑ x, (T.μ i).w x * if ∀ u ∈ (L81CrossKeys g).erase u₀,
      L81HitsTuple E G x (Θ u) then 1 else 0

/-- Gate threshold for a tag at a grid key. -/
def L81GateOpen {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (Θ : L81HiddenHistory n η₀ h N)
    (g : L81GridKey n η₀) (i : M.ι) : Prop :=
  L81DMinus T Θ g i ≥ Real.exp (-((n : ℝ) ^ (2 * tau8 η₀))) ∧
  L81DPlus T Θ g i ≥ (1 - Real.exp (-((n : ℝ) ^ (p / 2)))) * L81DMinus T Θ g i

/-- Normalizer of the tilted, gated tag distribution at key `g`. -/
noncomputable def L81GateZ {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (Θ : L81HiddenHistory n η₀ h N)
    (g : L81GridKey n η₀) : ℝ := by
  classical
  exact ∑ i, L81PosteriorWeight T (Θ g) i * L81DMinus T Θ g i *
    if L81GateOpen T Θ g i then 1 else 0

/-- Gated posterior tag law, with the original trimmed law as a total fallback on a null gate. -/
noncomputable def L81TiltedTagWeight {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (Θ : L81HiddenHistory n η₀ h N)
    (g : L81GridKey n η₀) (i : M.ι) : ℝ := by
  classical
  let z := L81GateZ T Θ g
  let a := L81PosteriorWeight T (Θ g) i * L81DMinus T Θ g i *
    if L81GateOpen T Θ g i then 1 else 0
  exact if z = 0 then T.weight i else a / z

/-- Anchor law `U_{g,i}`; the trimmed law is the total fallback if its conditioning mass vanishes. -/
noncomputable def L81AnchorWeight {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (Θ : L81HiddenHistory n η₀ h N)
    (g : L81GridKey n η₀) (i : M.ι) (x : Fin N) : ℝ := by
  classical
  let d := L81DPlus T Θ g i
  let hit := (∀ u ∈ L81CrossKeys g, L81HitsTuple E G x (Θ u)) ∧
    L81HitsTuple E G x (Θ g)
  exact if d = 0 then (T.μ i).w x else
    (T.μ i).w x * (if hit then 1 else 0) / d

/-- The four base gates (G1--G4) at one grid key. -/
def L81BaseGates {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (Θ : L81HiddenHistory n η₀ h N)
    (g : L81GridKey n η₀) : Prop :=
  (∀ i, L81PosteriorWeight T (Θ g) i ≤
      Real.exp ((h : ℝ) * (n : ℝ) ^ β + (n : ℝ) ^ (tau8 η₀ / 2)) * T.weight i) ∧
  (0.8 : ℝ) * L81AG h g ≤ L81GateZ T Θ g ∧
    L81GateZ T Θ g ≤ (1.2 : ℝ) * L81AG h g ∧
  (L81AG h g / 1.1 ≤ ∑ i, L81PosteriorWeight T (Θ g) i * L81DMinus T Θ g i ∧
    ∑ i, L81PosteriorWeight T (Θ g) i * L81DMinus T Θ g i ≤ 1.1 * L81AG h g) ∧
  (L81AG h g / 1.1 ≤ ∑ i, T.weight i * L81DMinus T Θ g i ∧
    ∑ i, T.weight i * L81DMinus T Θ g i ≤ 1.1 * L81AG h g) ∧
  ∀ u₀ ∈ L81CrossKeys g,
    (2 ^ (h : ℝ) * L81AG h g / 1.1 ≤
      ∑ i, L81PosteriorWeight T (Θ g) i * L81DMinusOmit T Θ g u₀ i ∧
      ∑ i, L81PosteriorWeight T (Θ g) i * L81DMinusOmit T Θ g u₀ i ≤
        1.1 * 2 ^ (h : ℝ) * L81AG h g) ∧
    (2 ^ (h : ℝ) * L81AG h g / 1.1 ≤
      ∑ i, T.weight i * L81DMinusOmit T Θ g u₀ i ∧
      ∑ i, T.weight i * L81DMinusOmit T Θ g u₀ i ≤ 1.1 * 2 ^ (h : ℝ) * L81AG h g)

/-- A finite hidden history fails a base gate at key `g`. -/
def L81GateFails {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (g : L81GridKey n η₀)
    (Θ : L81HiddenHistory n η₀ h N) : Prop := ¬ L81BaseGates T Θ g

/-- Cells are pairs of a grid key and a residual word. -/
abbrev L81Cell (n : ℕ) (η₀ : ℝ) := L81GridKey n η₀ × L81Residual n η₀

/-- A centre stores its sampled residual word and the finite centre-list identifier. -/
abbrev L81Centre (n : ℕ) (η₀ : ℝ) := L81Residual n η₀ × Fin (n ^ 10)

/-- Centre assignments for all cells. -/
abbrev L81Centres (n : ℕ) (η₀ : ℝ) := L81Cell n η₀ → L81Centre n η₀

/-- The tag selected at every cell. -/
abbrev L81Tags {N : ℕ} (M : TagMix N) (n : ℕ) (η₀ : ℝ) :=
  L81Cell n η₀ → M.ι

/-- The first-side anchor at every cell. -/
abbrev L81Anchors (N n : ℕ) (η₀ : ℝ) := L81Cell n η₀ → Fin N

/-- Number of centre IDs in an ordinary fan. -/
noncomputable def L81OrdinaryFanSize {n : ℕ} {η₀ : ℝ}
    (C : L81Centres n η₀) (c : L81Cell n η₀) : ℕ := by
  classical
  let ns := Finset.univ.filter fun d : L81Cell n η₀ =>
    c.1 = d.1 ∧ L81ResidualDistance c.2 d.2 ≤ 1
  exact (ns.image fun d => (C d).2).card

/-- Number of centre levels occupied in an ordinary fan. -/
noncomputable def L81OrdinaryLevelCount {n : ℕ} {η₀ : ℝ}
    (C : L81Centres n η₀) (c : L81Cell n η₀) : ℕ := by
  classical
  let ns := Finset.univ.filter fun d : L81Cell n η₀ =>
    c.1 = d.1 ∧ L81ResidualDistance c.2 d.2 ≤ 1
  exact (ns.image fun d => L81WordWeight (C d).1).card

/-- The centre law has the L3.8 fan property on every supported centre history. -/
def L81FanGood {n : ℕ} {η₀ : ℝ} (P : FinProb (L81Centres n η₀)) : Prop :=
  ∀ C, 0 < P.w C → ∀ c,
    L81OrdinaryFanSize C c ≤ Nat.ceil ((n : ℝ) ^ (tau8 η₀ / 8)) ∧
    L81OrdinaryLevelCount C c ≤ 2

/-- The random state produced by the L8.1 experiment. -/
abbrev L81ExperimentOutcome {N n : ℕ} {η₀ : ℝ} {h : ℕ} (M : TagMix N) :=
  ((L81HiddenHistory n η₀ h N × L81Centres n η₀) × L81Tags M n η₀) × L81Anchors N n η₀

/-- The finite experiment: independent hidden tuples, an L3.8 centre kernel, independently tilted tags,
and conditionally independent anchor samples from their explicit `U_{g,i}` weights. -/
structure L81Experiment {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) where
  centreKernel : L81HiddenHistory n η₀ h N → FinProb (L81Centres n η₀)
  centreFan : ∀ _Θ, L81FanGood (centreKernel _Θ)
  tagKernel : ∀ _Θ, L81Centres n η₀ → FinProb (L81Tags M n η₀)
  tagProduct : ∀ Θ C t, (tagKernel Θ C).w t =
    ∏ c, L81TiltedTagWeight T Θ c.1 (t c)
  anchorKernel : ∀ _Θ, L81Centres n η₀ → L81Tags M n η₀ → FinProb (L81Anchors N n η₀)
  anchorProduct : ∀ Θ C t w, (anchorKernel Θ C t).w w =
    ∏ c, L81AnchorWeight T Θ c.1 (t c) (w c)

/-- Sample space of the experiment. -/
abbrev L81ExperimentSpace {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (_T : L81TrimmedMix I h) := @L81ExperimentOutcome N n η₀ h M

/-- Joint law of the complete sequential experiment. -/
noncomputable def L81ExperimentLaw {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (ex : L81Experiment T) : FinProb (L81ExperimentSpace T) := by
  classical
  let hLaw := L81HiddenLaw T
  let hc := FinProb.bind hLaw ex.centreKernel
  let hct := FinProb.bind hc (fun q => ex.tagKernel q.1 q.2)
  let hcta := FinProb.bind hct (fun q => ex.anchorKernel q.1.1 q.1.2 q.2)
  exact FinProb.map hcta (fun q => q)

end HypercubeRamsey
