import HypercubeRamsey.PartC.Mesh

/-!
# Section 14 internal slice-solver interface (D14.S)

The solver stores primitive finite records and deterministic functions of
those records. Odd words represent the paper's syndrome fibers, and even
words represent selection sites; the geometry lemmas that identify their
fiber multiplicities are separate proof-tool work.
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

/-- Internal cube words for one patch. -/
abbrev IWord {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) := CubePos (𝒯.P i).h

/-- Even internal words, used as the solver's selection sites. -/
def EvenRole {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) :=
  {w : IWord 𝒯 i // IsEvenRole w}

/-- Internal roles form finite subtypes of the cube words. -/
noncomputable instance instEvenRoleFintype {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Fintype (EvenRole 𝒯 i) :=
  Fintype.subtype (Finset.univ.filter fun w : IWord 𝒯 i => IsEvenRole w) (by intro w; simp)

/-- One odd-role syndrome fiber, represented by its projected even site and its members. -/
def Group {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) :=
  {p : IWord 𝒯 i × Finset (IWord 𝒯 i) //
    IsEvenRole p.1 ∧ p.2.card = (𝒯.P i).h ∧
      (∀ z ∈ p.2, ¬ IsEvenRole z) ∧
      (∀ z ∈ p.2, hammingDist z p.1 = 1)}

/-- The even site indexing the group fiber. -/
def groupCenter {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} (g : Group 𝒯 i) : EvenRole 𝒯 i :=
  ⟨g.1.1, g.2.1⟩

/-- Odd internal words in one syndrome fiber. -/
def groupFiber {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} (g : Group 𝒯 i) : Finset (IWord 𝒯 i) := g.1.2

/-- Group fibers form a partition of all odd internal roles. -/
def GroupPartition {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Prop :=
  ∀ z : IWord 𝒯 i, ¬ IsEvenRole z → ∃! g : Group 𝒯 i, z ∈ groupFiber g

noncomputable instance instGroupFintype {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Fintype (Group 𝒯 i) :=
  Fintype.subtype
    (Finset.univ.filter fun p : IWord 𝒯 i × Finset (IWord 𝒯 i) =>
      IsEvenRole p.1 ∧ p.2.card = (𝒯.P i).h ∧
        (∀ z ∈ p.2, ¬ IsEvenRole z) ∧ ∀ z ∈ p.2, hammingDist z p.1 = 1)
    (by intro p; simp)

/-- A physical bin of a patch. -/
def Bin {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) :=
  {B : Finset (Fin (T.S.N k)) // B ∈ (𝒯.P i).bins.parts}

/-- A physical-bin subtype is finite because the host and bin partition are finite. -/
noncomputable instance instBinFintype {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Fintype (Bin 𝒯 i) :=
  Fintype.subtype (𝒯.P i).bins.parts (by intro B; rfl)

/-- Equality on physical bins is decidable. -/
noncomputable instance instBinDecidableEq {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : DecidableEq (Bin 𝒯 i) := Classical.decEq _

/-- Internal label tuple for one slice. -/
abbrev InternalLabels {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) := Fin (𝒯.P i).h → Fin (T.S.N k)

/-- Coordinate domain consulted by a group or site within a slice record. -/
def recordNear {α : Type*} [Fintype α] {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} {i : Fin 𝒯.m}
    (loc : α → IWord 𝒯 i) (center : IWord 𝒯 i) : Finset α :=
  Finset.univ.filter fun r => hammingDist (loc r) center ≤ 10

/-- Abstract slice solver satisfying the uniformity, support, cap, locality,
and symmetry interface (S1)–(S8) from D14.S. -/
structure SliceSolver (κ : CConsts) {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k)
    (i : Fin 𝒯.m) (mesh : Mesh 𝒯) (p : mesh.Param) where
  Rec : Type
  [recFin : Fintype Rec]
  loc : Rec → IWord 𝒯 i
  group_partition : GroupPartition 𝒯 i
  Val : Rec → Type
  [valFin : ∀ r, Fintype (Val r)]
  lawRec : ∀ r, Val r → ℝ
  lawRec_nonneg : ∀ r v, 0 ≤ lawRec r v
  lawRec_sum : ∀ r, ∑ v, lawRec r v = 1
  q : Group 𝒯 i → (∀ r, Val r) → Bin 𝒯 i → ℝ
  U : Group 𝒯 i → (∀ r, Val r) → Bin 𝒯 i → Fin (T.S.N k) → ℝ
  σ : EvenRole 𝒯 i → (∀ r, Val r) → InternalLabels 𝒯 i → Fin (T.S.N k) → ℝ
  Hgood : EvenRole 𝒯 i → (∀ r, Val r) → Prop
  pint : (∀ r, Val r) → FinLaw (InternalLabels 𝒯 i)
  q_nonneg : ∀ g W D, 0 ≤ q g W D
  q_sum : ∀ g W, ∑ D : Bin 𝒯 i, q g W D = 1
  U_nonneg : ∀ g W D y, 0 ≤ U g W D y
  U_sum : ∀ g W D, ∑ y, U g W D y = 1
  U_support : ∀ g W D y, U g W D y ≠ 0 → y ∈ D.1
  /-- Odd marginal law `p_g^W = ∑_D q_g^W(D) U_g^W(D)`. -/
  oddMarginal : Group 𝒯 i → (∀ r, Val r) → Fin (T.S.N k) → ℝ :=
    fun g W y => ∑ D : Bin 𝒯 i, q g W D * U g W D y
  q_cap : ∀ g W D,
    q g W D ≤ 4 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) *
      (𝒯.P i).d / (𝒯.P i).M
  marginal_cap : ∀ g W y,
    oddMarginal g W y ≤
      8 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) / (𝒯.P i).M
  U_support_size : ∀ g W D, q g W D > 0 →
    ((Finset.univ.filter fun y => U g W D y ≠ 0).card : ℝ) ≥
      (1 / 2 : ℝ) * (𝒯.P i).d * Real.exp (-1.5 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)
  σ_nonneg : ∀ v W ys x, 0 ≤ σ v W ys x
  σ_mass : ∀ v W ys, ∑ x, σ v W ys x ≤ 1
  /-- S2: rows are supported on one positive-weight cleaned corner and every internal common neighbour. -/
  σ_support : ∀ v W ys x, σ v W ys x ≠ 0 →
    ∃ v' : mesh.V, 0 < mesh.wt v' p ∧ x ∈ mesh.corner v' i ∧
      ∀ l, Hits (T.S.E k) 𝒯.c x (ys l)
  /-- S3: the pointwise cap on each even row. -/
  σ_cap : ∀ v W ys x,
    (T.S.N k : ℝ) * σ v W ys x ≤
      2 ^ (𝒯.P i).h * Real.exp (-500 * 𝒯.gain i)
  /-- S4: average row mass under primitive records and internal reference labels. -/
  σ_mean : ∀ v x,
    (FinLaw.pi (fun r => ⟨lawRec r, lawRec_nonneg r, lawRec_sum r⟩)).E
      (fun W => (pint W).E (fun ys => σ v W ys x)) ≤ rowMeanConstant κ / (𝒯.P i).M
  /-- S5: on a good record, the reference experiment sees a zero row with probability at most epsilon. -/
  Hgood_zero : ∀ v W, Hgood v W →
    (pint W).pr (fun ys => σ v W ys = 0) ≤ sliceEps κ (𝒯.P i).h
  /-- S5: simultaneous local validity fails only with the stated stretched-exponential probability. -/
  Hgood_bad :
    (FinLaw.pi (fun r => ⟨lawRec r, lawRec_nonneg r, lawRec_sum r⟩)).pr
      (fun W => ∃ v : EvenRole 𝒯 i, ¬ Hgood v W) ≤
        Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14))
  /-- S6: odd bin probabilities depend only on records within distance ten of the group representative. -/
  q_local : ∀ g W W',
    (∀ r, hammingDist (loc r) (groupCenter g).1 ≤ 10 → W r = W' r) → q g W = q g W'
  /-- S6: in-bin laws have the same local consultation domain. -/
  U_local : ∀ g W W' D,
    (∀ r, hammingDist (loc r) (groupCenter g).1 ≤ 10 → W r = W' r) → U g W D = U g W' D
  /-- S6: even rows consult only records near their site. -/
  σ_local : ∀ v W W' ys,
    (∀ r, hammingDist (loc r) v.1 ≤ 10 → W r = W' r) → σ v W ys = σ v W' ys
  /-- S6: local validity tests consult only records near their site. -/
  Hgood_local : ∀ v W W',
    (∀ r, hammingDist (loc r) v.1 ≤ 10 → W r = W' r) → (Hgood v W ↔ Hgood v W')
  /-- S7: syndrome-zero symmetry in the form consumed by the averaged odd marginals. -/
  averaged_marginal_invariant : ∀ g g' y,
    (∑ W, (FinLaw.pi (fun r => ⟨lawRec r, lawRec_nonneg r, lawRec_sum r⟩)).w W *
      oddMarginal g W y) =
    (∑ W, (FinLaw.pi (fun r => ⟨lawRec r, lawRec_nonneg r, lawRec_sum r⟩)).w W *
      oddMarginal g' W y)

end HypercubeRamsey
