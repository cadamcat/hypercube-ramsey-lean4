import HypercubeRamsey.PartC.Mesh

/-!
# Section 14 internal slice-solver interface (D14.S)

The solver stores primitive finite records and deterministic functions of
those records (sections/14 lines 16–46, 75–95, 141–167). Odd groups are the
fibres of the projection `ψ(z) = z ⊕ e_{s(z)}`: one group per syndrome-zero
even internal word, whose fibre is its `h` neighbours (P14.1a; a partition of
the odd words when `h` is a power of two). Selection sites are the even
internal words. The internal reference experiment is defined from the bin and
in-bin laws (independent group bins, then independent role labels), not chosen
separately. Records have laws depending continuously on the parameter point;
the bin laws, rows and tests are fixed functions of the records (S8).

The solver of a patch uses the internal parity convention (even role = even
number of `true` internal coordinates). A slice whose fixed outer word has odd
parity uses the same solver transported by the syndrome-zero, parity-changing
translation `z ↦ z ⊕ e₀` (sections/14 lines 35, 95).
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

/-- Binary syndrome `s(z) = ⨁_{z_l = 1} l` of an internal word, as its vector of binary digits
(bit `j` of `s(z)` is the parity of the indices `l` with `z_l = 1` and bit `j` of `l` set). -/
def wordSyndrome {h : ℕ} (z : CubePos h) : ℕ → ZMod 2 := fun j =>
  ∑ l : Fin h, if z l = true ∧ l.val.testBit j = true then 1 else 0

/-- One odd group (P14.1a): a syndrome-zero even internal word; its fibre is its `h` neighbours. -/
def Group {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) :=
  {w : IWord 𝒯 i // IsEvenRole w ∧ wordSyndrome w = 0}

/-- The even site indexing the group fiber. -/
def groupCenter {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} (g : Group 𝒯 i) : EvenRole 𝒯 i :=
  ⟨g.1, g.2.1⟩

/-- Odd internal words in one group: the `ψ`-fibre, i.e. all neighbours of the centre. -/
def groupFiber {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} (g : Group 𝒯 i) : Finset (IWord 𝒯 i) :=
  Finset.univ.image (flipPos g.1)

/-- Group fibers form a partition of all odd internal roles (P14.1a(ii); true when `h` is a power
of two). -/
def GroupPartition {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Prop :=
  ∀ z : IWord 𝒯 i, ¬ IsEvenRole z → ∃! g : Group 𝒯 i, z ∈ groupFiber g

noncomputable instance instGroupFintype {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Fintype (Group 𝒯 i) :=
  Fintype.subtype
    (Finset.univ.filter fun w : IWord 𝒯 i => IsEvenRole w ∧ wordSyndrome w = 0)
    (by intro w; simp)

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

/-- Internal label tuple for one even star, indexed by the flipped internal coordinate. -/
abbrev InternalLabels {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) := Fin (𝒯.P i).h → Fin (T.S.N k)

/-- The labels of the `h` internal neighbours of `v`, read from a labelling of all internal words. -/
def nbrLabels {h N : ℕ} (v : CubePos h) (lab : CubePos h → Fin N) : Fin h → Fin N :=
  fun l => lab (flipPos v l)

/-- Consultation radius `10ρh` of the local rules (sections/14 line 95). -/
noncomputable def recordNear {α : Type*} [Fintype α] {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} {i : Fin 𝒯.m}
    (loc : α → IWord 𝒯 i) (center : IWord 𝒯 i) : Finset α :=
  Finset.univ.filter fun r => (hammingDist (loc r) center : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h

/-- Product law of independent primitive records. -/
noncomputable def recordLaw {R : Type*} [Fintype R] [DecidableEq R] {V : R → Type*}
    [∀ r, Fintype (V r)] (w : ∀ r, V r → ℝ) (h0 : ∀ r v, 0 ≤ w r v) (h1 : ∀ r, ∑ v, w r v = 1) :
    FinLaw (∀ r, V r) :=
  FinLaw.pi fun r => ⟨w r, h0 r, h1 r⟩

/-- Internal reference experiment of one slice (sections/14 line 75): independent group bins
`D_g ∼ q_g`, then independent labels of all internal words, the word `z` drawn from the in-bin law of
its group's bin. Only odd words are read; even words carry unused coordinates. -/
noncomputable def internalRefLaw {Gp Bn Wd : Type*} [Fintype Gp] [DecidableEq Gp] [Fintype Bn]
    [Fintype Wd] [DecidableEq Wd] {N : ℕ}
    (q : Gp → Bn → ℝ) (hq0 : ∀ g D, 0 ≤ q g D) (hq1 : ∀ g, ∑ D, q g D = 1)
    (U : Gp → Bn → Fin N → ℝ) (hU0 : ∀ g D y, 0 ≤ U g D y) (hU1 : ∀ g D, ∑ y, U g D y = 1)
    (grp : Wd → Gp) : FinLaw ((Gp → Bn) × (Wd → Fin N)) :=
  FinLaw.bind (FinLaw.pi fun g => ⟨q g, hq0 g, hq1 g⟩)
    (fun D => FinLaw.pi fun z => ⟨U (grp z) (D (grp z)), hU0 _ _, hU1 _ _⟩)

/-- D14.S: slice solver satisfying (S1)–(S8). `lawRec p` is the record law at parameter point `p`;
everything else is a function of the records only. -/
structure SliceSolver (κ : CConsts) {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k)
    (i : Fin 𝒯.m) (mesh : Mesh 𝒯) where
  Rec : Type
  [recFin : Fintype Rec]
  loc : Rec → IWord 𝒯 i
  Val : Rec → Type
  [valFin : ∀ r, Fintype (Val r)]
  lawRec : mesh.Param → ∀ r, Val r → ℝ
  lawRec_nonneg : ∀ p r v, 0 ≤ lawRec p r v
  lawRec_sum : ∀ p r, ∑ v, lawRec p r v = 1
  /-- (S8): the parameter enters only through continuous record laws. -/
  lawRec_cont : ∀ r v, Continuous fun p => lawRec p r v
  /-- The group of each internal word (meaningful on odd words). -/
  groupOf : IWord 𝒯 i → Group 𝒯 i
  groupOf_spec : ∀ z, ¬ IsEvenRole z → z ∈ groupFiber (groupOf z)
  group_partition : GroupPartition 𝒯 i
  q : Group 𝒯 i → (∀ r, Val r) → Bin 𝒯 i → ℝ
  U : Group 𝒯 i → (∀ r, Val r) → Bin 𝒯 i → Fin (T.S.N k) → ℝ
  σ : EvenRole 𝒯 i → (∀ r, Val r) → InternalLabels 𝒯 i → Fin (T.S.N k) → ℝ
  Hgood : EvenRole 𝒯 i → (∀ r, Val r) → Prop
  q_nonneg : ∀ g W D, 0 ≤ q g W D
  q_sum : ∀ g W, ∑ D : Bin 𝒯 i, q g W D = 1
  U_nonneg : ∀ g W D y, 0 ≤ U g W D y
  U_sum : ∀ g W D, ∑ y, U g W D y = 1
  U_support : ∀ g W D y, U g W D y ≠ 0 → y ∈ D.1
  /-- (S1), eq:source-13. -/
  q_cap : ∀ g W D,
    q g W D ≤ 4 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) *
      (𝒯.P i).d / (𝒯.P i).M
  /-- (S1): the odd marginal `p_g^W = ∑_D q_g^W(D) U_g^W(D)` is capped. -/
  marginal_cap : ∀ g W y,
    ∑ D : Bin 𝒯 i, q g W D * U g W D y ≤
      8 * Real.exp (2 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) / (𝒯.P i).M
  U_support_size : ∀ g W D, q g W D > 0 →
    ((Finset.univ.filter fun y => U g W D y ≠ 0).card : ℝ) ≥
      (1 / 2 : ℝ) * (𝒯.P i).d * Real.exp (-1.5 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)
  /-- Atom bound of the uniform-subset law, used by the conditional injection stages. -/
  U_atom_cap : ∀ g W D y, 0 < q g W D →
    U g W D y ≤ 2 * Real.exp (1.5 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) / (𝒯.P i).d
  σ_nonneg : ∀ v W ys x, 0 ≤ σ v W ys x
  /-- A nonzero even row is a probability law. -/
  σ_prob : ∀ v W ys, σ v W ys ≠ 0 → ∑ x, σ v W ys x = 1
  /-- (S2): a nonzero row is supported in one cleaned corner support, of a vertex active at every
  parameter point charging the records, and on common neighbours of every internal label. -/
  σ_support : ∀ v W ys, σ v W ys ≠ 0 →
    ∃ v' : mesh.V,
      (∀ p, 0 < (recordLaw (lawRec p) (lawRec_nonneg p) (lawRec_sum p)).w W →
        0 < mesh.wt v' p) ∧
      ∀ x, σ v W ys x ≠ 0 → x ∈ mesh.corner v' i ∧ ∀ l, Hits (T.S.E k) 𝒯.c x (ys l)
  /-- (S3): the pointwise cap on each even row. -/
  σ_cap : ∀ v W ys x,
    (T.S.N k : ℝ) * σ v W ys x ≤
      2 ^ (𝒯.P i).h * Real.exp (-500 * 𝒯.gain i)
  /-- (S4): average row mass under the records and the internal reference experiment. -/
  σ_mean : ∀ p (v : EvenRole 𝒯 i) x,
    (recordLaw (lawRec p) (lawRec_nonneg p) (lawRec_sum p)).E (fun W =>
      (internalRefLaw (fun g => q g W) (fun g => q_nonneg g W) (fun g => q_sum g W)
        (fun g => U g W) (fun g => U_nonneg g W) (fun g => U_sum g W) groupOf).E
        (fun ω => σ v W (nbrLabels v.1 ω.2) x)) ≤ rowMeanConstant κ / (𝒯.P i).M
  /-- (S5): on a passing test, the reference experiment sees a zero row with probability at most
  `ε_i`. -/
  Hgood_zero : ∀ v W, Hgood v W →
    (internalRefLaw (fun g => q g W) (fun g => q_nonneg g W) (fun g => q_sum g W)
        (fun g => U g W) (fun g => U_nonneg g W) (fun g => U_sum g W) groupOf).pr
      (fun ω => σ v W (nbrLabels v.1 ω.2) = 0) ≤ sliceEps κ (𝒯.P i).h
  /-- (S5): the tests hold simultaneously in a slice except with the stated probability. -/
  Hgood_bad : ∀ p,
    (recordLaw (lawRec p) (lawRec_nonneg p) (lawRec_sum p)).pr
      (fun W => ∃ v : EvenRole 𝒯 i, ¬ Hgood v W) ≤
        Real.exp (-Real.rpow ((𝒯.P i).h : ℝ) (1 + κ.c14))
  /-- (S6): bin probabilities read only records within `10ρh` of the group's centre. -/
  q_local : ∀ g W W',
    (∀ r, (hammingDist (loc r) (groupCenter g).1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) →
      q g W = q g W'
  /-- (S6): in-bin laws have the same consultation domain. -/
  U_local : ∀ g W W' D,
    (∀ r, (hammingDist (loc r) (groupCenter g).1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) →
      U g W D = U g W' D
  /-- (S6): even rows read only records within `10ρh` of their site. -/
  σ_local : ∀ v W W' ys,
    (∀ r, (hammingDist (loc r) v.1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) →
      σ v W ys = σ v W' ys
  /-- (S6): local tests read only records within `10ρh` of their site. -/
  Hgood_local : ∀ v W W',
    (∀ r, (hammingDist (loc r) v.1 : ℝ) ≤ 10 * κ.ρ * (𝒯.P i).h → W r = W' r) →
      (Hgood v W ↔ Hgood v W')
  /-- (S7): syndrome-zero symmetry, in the form consumed: the mean odd marginal does not depend on
  the group. -/
  averaged_marginal_invariant : ∀ p g g' y,
    (recordLaw (lawRec p) (lawRec_nonneg p) (lawRec_sum p)).E
        (fun W => ∑ D : Bin 𝒯 i, q g W D * U g W D y) =
      (recordLaw (lawRec p) (lawRec_nonneg p) (lawRec_sum p)).E
        (fun W => ∑ D : Bin 𝒯 i, q g' W D * U g' W D y)
  /-- L14.3: in low cluster mode the records charged at any parameter point are few. -/
  low_support : 𝒯.mode = .lowCluster → ∀ p,
    (((Finset.univ.filter fun W =>
        0 < (recordLaw (lawRec p) (lawRec_nonneg p) (lawRec_sum p)).w W).card : ℕ) : ℝ) ≤
      Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ))

namespace SliceSolver

variable {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}

instance instRecFintype (S : SliceSolver κ 𝒯 i mesh) : Fintype S.Rec := S.recFin

instance instValFintype (S : SliceSolver κ 𝒯 i mesh) : ∀ r, Fintype (S.Val r) := S.valFin

/-- Record law `P_W` at a parameter point. -/
noncomputable def recLaw (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) : FinLaw (∀ r, S.Val r) :=
  recordLaw (S.lawRec p) (S.lawRec_nonneg p) (S.lawRec_sum p)

/-- Internal reference experiment `Pint(· ∣ W)`: group bins and labels of all internal words. -/
noncomputable def refLaw (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) :
    FinLaw ((Group 𝒯 i → Bin 𝒯 i) × (IWord 𝒯 i → Fin (T.S.N k))) :=
  internalRefLaw (fun g => S.q g W) (fun g => S.q_nonneg g W) (fun g => S.q_sum g W)
    (fun g => S.U g W) (fun g => S.U_nonneg g W) (fun g => S.U_sum g W) S.groupOf

/-- Odd marginal law `p_g^W = ∑_D q_g^W(D) U_g^W(D)`. -/
noncomputable def oddMarginal (S : SliceSolver κ 𝒯 i mesh) (g : Group 𝒯 i) (W : ∀ r, S.Val r)
    (y : Fin (T.S.N k)) : ℝ :=
  ∑ D : Bin 𝒯 i, S.q g W D * S.U g W D y

/-- Unrestricted mean odd law `π⁰ᵢ = E_W p_g^W` (sections/14 line 175). -/
noncomputable def oddMean (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) (g : Group 𝒯 i)
    (y : Fin (T.S.N k)) : ℝ :=
  (S.recLaw p).E fun W => S.oddMarginal g W y

/-- The even star at `v` is incident to group `g`. -/
def Incident (v : EvenRole 𝒯 i) (g : Group 𝒯 i) : Prop :=
  ∃ l, flipPos v.1 l ∈ groupFiber g

/-- Pretrim bins `𝓑_g(W)` (sections/14 lines 177–182): positive bins at which every incident star
fails, given the bin, with reference probability at most `√ε_i`. -/
noncomputable def pretrimBins (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (g : Group 𝒯 i) :
    Finset (Bin 𝒯 i) :=
  Finset.univ.filter fun D => 0 < S.q g W D ∧ ∀ v : EvenRole 𝒯 i, Incident v g →
    (S.refLaw W).pr (fun ω => ω.1 g = D ∧ S.σ v W (nbrLabels v.1 ω.2) = 0) ≤
      Real.sqrt (sliceEps κ (𝒯.P i).h) * S.q g W D

/-- Pretrimmed bin law `q_g^{in,W}`. -/
noncomputable def qin (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (g : Group 𝒯 i)
    (D : Bin 𝒯 i) : ℝ :=
  if D ∈ S.pretrimBins W g then S.q g W D / ∑ D' ∈ S.pretrimBins W g, S.q g W D' else 0

/-- All local tests of the slice pass. -/
def AllGood (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) : Prop := ∀ v, S.Hgood v W

/-- Low-mode output `π^out_i`: mean of `∑_D q_g^{in,W}(D) U_g^W(D)` under the record law
conditioned on all tests (sections/14 lines 177–188). -/
noncomputable def lowOut (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) (g : Group 𝒯 i)
    (y : Fin (T.S.N k)) : ℝ :=
  (∑ W, (S.recLaw p).w W *
      (if S.AllGood W then ∑ D : Bin 𝒯 i, S.qin W g D * S.U g W D y else 0)) /
    (S.recLaw p).pr S.AllGood

end SliceSolver

end HypercubeRamsey
