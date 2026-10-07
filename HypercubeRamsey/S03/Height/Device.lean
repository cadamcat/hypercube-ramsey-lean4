import HypercubeRamsey.Framework.FinProb
import OAI.Combinatorics.Ramsey.Hypercube

/-!
# D3.8: finite height-device experiment

The parameter `n` is an abstract asymptotic parameter. Consumers may instantiate it with the ambient
parameter used in their section. Probabilities use the repository's clamped Bernoulli law; the admissibility
hypotheses in the selection lemmas ensure its parameters are in `[0,1]` in the intended regime.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey
open scoped BigOperators

namespace FinProb

/-- Bernoulli law on `Bool`, with its parameter clamped to `[0,1]` for totality. -/
noncomputable def bernoulli (q : ℝ) : FinProb Bool where
  w b := if b then max 0 (min q 1) else 1 - max 0 (min q 1)
  nonneg b := by
    cases b
    · simp only [Bool.false_eq_true, ite_false, sub_nonneg]
      exact max_le zero_le_one (min_le_right _ _)
    · simp only [ite_true]
      exact le_max_left _ _
  sum_eq_one := by simp

/-- Product of two finite probability laws. -/
noncomputable def prod {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) : FinProb (α × β) where
  w ab := P.w ab.1 * Q.w ab.2
  nonneg ab := mul_nonneg (P.nonneg _) (Q.nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp [← Finset.mul_sum, Q.sum_eq_one, P.sum_eq_one]

/-- Uniform probability on every element of a nonempty finite type. -/
noncomputable def uniformAll {Ω : Type*} [Fintype Ω] (hΩ : Nonempty Ω) : FinProb Ω where
  w _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_eq_one := by
    letI : Nonempty Ω := hΩ
    have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω).ne'
    simp [Finset.sum_const, nsmul_eq_mul, hcard]

end FinProb

/-- The parameters of one finite instance of the height device. -/
structure HDParams where
  n : ℕ
  d : ℕ
  D : ℕ
  r : ℕ
  H : ℕ
  lam : ℝ
  b₀ : ℝ
  b : ℝ

namespace HDParams

variable (p : HDParams)

/-- A center ID consists of a cube location and a level in `0..H`. -/
abbrev Loc := CubeVertex p.d × Fin (p.H + 1)

/-- The set of queried cube vertices. -/
abbrev Sites := Finset (CubeVertex p.d)

/-- A complete eligibility map, defined at every site and every level. -/
abbrev EligMap := CubeVertex p.d → Fin (p.H + 1) → Finset p.Loc

/-- Volume of a radius-`r` Hamming ball in the `d`-cube. -/
def V : ℕ := ∑ i ∈ Finset.range (p.r + 1), Nat.choose p.d i

/-- Legal eligibility at one site-level: prospective, on the same level, in the radius-`r` ball, and large. -/
def LegalAt (P : p.Loc → Bool) (E : p.EligMap) (v : CubeVertex p.d)
    (j : Fin (p.H + 1)) : Prop :=
  (∀ ℓ ∈ E v j, P ℓ = true ∧ ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r) ∧
    p.lam / 3 ≤ ((E v j).card : ℝ)

/-- Legal eligibility on a queried domain, at every level. -/
def Legal (P : p.Loc → Bool) (E : p.EligMap) (dom : p.Sites) : Prop :=
  ∀ v ∈ dom, ∀ j, p.LegalAt P E v j

/-- A site-level is bad if its eligible set has no active ID or its `(r+D)`-ball is overcrowded. -/
def Bad (P A : p.Loc → Bool) (E : p.EligMap) (v : CubeVertex p.d)
    (j : Fin (p.H + 1)) : Prop :=
  (∀ ℓ ∈ E v j, A ℓ = false) ∨
    (p.n : ℝ) ^ p.b < ((Finset.univ.filter (fun u : CubeVertex p.d =>
      P (u, j) = true ∧ A (u, j) = true ∧ hammingDist u v ≤ p.r + p.D)).card : ℝ)

/-- The level-indexed form of `Bad`; levels beyond `H` are not bad. -/
def BadN (P A : p.Loc → Bool) (E : p.EligMap) (v : CubeVertex p.d) (j : ℕ) : Prop :=
  ∃ hj : j < p.H + 1, p.Bad P A E v ⟨j, hj⟩

/-- A path may consult only queried sites in the radius-`R` ball around its query. -/
inductive Reach (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap)
    (vq : CubeVertex p.d) (R : ℕ) : CubeVertex p.d → ℕ → Prop
  | start (v : CubeVertex p.d) : v ∈ Sites → hammingDist v vq ≤ R →
      Reach Sites P A E vq R v 0
  | up (v : CubeVertex p.d) (j : ℕ) (hj : j < p.H) :
      Reach Sites P A E vq R v j → p.BadN P A E v j →
      Reach Sites P A E vq R v (j + 1)
  | down (v v' : CubeVertex p.d) (j : ℕ) :
      Reach Sites P A E vq R v (j + 1) → v' ∈ Sites → hammingDist v' vq ≤ R →
      hammingDist v v' ≤ p.D → Reach Sites P A E vq R v' j

open Classical in
/-- Maximum reachable level at a query, with consultation radius `R`. -/
noncomputable def height (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap)
    (R : ℕ) (vq : CubeVertex p.d) : ℕ :=
  ((Finset.range (p.H + 1)).filter
    (fun j => p.Reach Sites P A E vq R vq j)).sup id

/-- Long consultation radius from D3.8. -/
def Rlong : ℕ := 2 * p.D * p.H

/-- Short consultation radius for a sample size `m`. -/
def Rshort (m : ℕ) : ℕ := p.D * Nat.sqrt m

/-- Queried sites in the spatial consultation ball around `v`. -/
def domBall (Sites : p.Sites) (v : CubeVertex p.d) (R : ℕ) : p.Sites :=
  Sites.filter (fun u => hammingDist u v ≤ R)

/-- The four global height properties in L3.8(1). -/
def GoodHeights (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap) : Prop :=
  ∀ v ∈ Sites,
    p.height Sites P A E p.Rlong v < p.H ∧
    ¬ p.BadN P A E v (p.height Sites P A E p.Rlong v) ∧
    ∀ v' ∈ Sites, hammingDist v v' ≤ p.D →
      |(p.height Sites P A E p.Rlong v : ℤ) - p.height Sites P A E p.Rlong v'| ≤ 1

/-- Product law of the independent prospective-center positions. -/
noncomputable def posLaw : FinProb (p.Loc → Bool) :=
  FinProb.pi (fun _ => FinProb.bernoulli (p.lam / (p.V : ℝ)))

/-- Product law of the independent activations. -/
noncomputable def actLaw : FinProb (p.Loc → Bool) :=
  FinProb.pi (fun _ => FinProb.bernoulli ((p.n : ℝ) ^ p.b₀ / p.lam))

/-- Positions with an optional specified ID forced present; other positions retain their product law. -/
noncomputable def posLawForced (forced : Option p.Loc) : FinProb (p.Loc → Bool) :=
  FinProb.pi (fun ℓ =>
    if forced = some ℓ then FinProb.bernoulli 1 else FinProb.bernoulli (p.lam / (p.V : ℝ)))

/-- A permutation of all center IDs, used to give distinct priorities at one site-level. -/
abbrev TiePerm := Equiv.Perm (Fin (Fintype.card p.Loc))

/-- An independent priority permutation for every site-level. -/
abbrev Ties := p.Loc → p.TiePerm

/-- Priority assigned to ID `ℓ` when queried at site-level `x`. -/
noncomputable def priority (τ : p.Ties) (x ℓ : p.Loc) : Fin (Fintype.card p.Loc) :=
  τ x (Fintype.equivFin p.Loc ℓ)

/-- Product law of independent uniform priority permutations. -/
noncomputable def tieLaw : FinProb p.Ties := by
  classical
  let U : FinProb p.TiePerm := FinProb.uniformAll ⟨1⟩
  exact FinProb.pi (fun _ => U)

open Classical in
/-- Selection at radius `R`: no choice at the top or at a bad level; otherwise take the least-priority
eligible active ID. -/
noncomputable def selectionAt (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap)
    (τ : p.Ties) (R : ℕ) (v : CubeVertex p.d) : Option p.Loc := by
  let j := p.height Sites P A E R v
  if hj : j < p.H then
    let j' : Fin (p.H + 1) := ⟨j, by omega⟩
    if hbad : p.Bad P A E v j' then
      exact none
    else
      let active := (E v j').filter (fun ℓ => A ℓ = true)
      let priorities := active.image (fun ℓ => p.priority τ (v, j') ℓ)
      if hne : priorities.Nonempty then
        let q := priorities.min' hne
        have hq : q ∈ priorities := Finset.min'_mem priorities hne
        let hmem : ∃ ℓ, ℓ ∈ active ∧ p.priority τ (v, j') ℓ = q :=
          Finset.mem_image.mp hq
        exact some (Classical.choose hmem)
      else
        exact none
  else
    exact none

/-- The usual selection rule uses the long consultation radius. -/
noncomputable def selection (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap)
    (τ : p.Ties) (v : CubeVertex p.d) : Option p.Loc :=
  p.selectionAt Sites P A E τ p.Rlong v

/-- Complete finite experiment law for positions, activations, and tie priorities. -/
noncomputable def experimentLaw : FinProb (((p.Loc → Bool) × (p.Loc → Bool)) × p.Ties) :=
  (p.posLaw.prod p.actLaw).prod p.tieLaw

end HDParams

end HypercubeRamsey
