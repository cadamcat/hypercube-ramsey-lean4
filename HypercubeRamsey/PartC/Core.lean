import HypercubeRamsey.Framework.PartC

/-!
# Shared finite probability and cube vocabulary for Part C

F-FinProb and F-Cube definitions for the Section 12–18 interfaces.

The finite laws in Sections 14–18 are represented by explicit weights.  This
module keeps that API separate from `FinProb`, whose names and interfaces are
used by the earlier framework.
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

/-- A probability law on a finite type, in the notation used by Part C. -/
structure FinLaw (Ω : Type*) [Fintype Ω] where
  w : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ w ω
  sum_one : ∑ ω, w ω = 1

namespace FinLaw

variable {Ω : Type*} [Fintype Ω]

/-- Expectation of a real-valued function under an explicit finite law. -/
noncomputable def E (P : FinLaw Ω) (F : Ω → ℝ) : ℝ := ∑ ω, P.w ω * F ω

/-- Probability of a predicate under an explicit finite law. -/
noncomputable def pr (P : FinLaw Ω) (A : Ω → Prop) : ℝ :=
  ∑ ω, if A ω then P.w ω else 0

/-- Product law on a dependent finite product. -/
noncomputable def pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i)) :
    FinLaw (∀ i, Ω i) where
  w ω := ∏ i, (P i).w (ω i)
  nonneg ω := Finset.prod_nonneg fun i _ => (P i).nonneg (ω i)
  sum_one := by
    rw [← Fintype.prod_sum]
    simp [FinLaw.sum_one]

/-- Sequential sampling: draw from `P`, then draw from `K` at the first result. -/
noncomputable def bind {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) : FinLaw (α × β) where
  w ab := P.w ab.1 * (K ab.1).w ab.2
  nonneg ab := mul_nonneg (P.nonneg _) ((K ab.1).nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ a, ∑ b, P.w a * (K a).w b) =
          ∑ a, P.w a * (∑ b, (K a).w b) := by
            congr 1
            funext a
            rw [Finset.mul_sum]
      _ = ∑ a, P.w a := by simp [FinLaw.sum_one]
      _ = 1 := P.sum_one

/-- Dependent sequential sampling, whose second outcome type may depend on the first. -/
noncomputable def bindD {α : Type*} {β : α → Type*} [Fintype α]
    [∀ a, Fintype (β a)] (P : FinLaw α) (K : ∀ a, FinLaw (β a)) :
    FinLaw (Sigma β) where
  w ab := P.w ab.1 * (K ab.1).w ab.2
  nonneg ab := mul_nonneg (P.nonneg _) ((K ab.1).nonneg _)
  sum_one := by
    rw [Fintype.sum_sigma]
    calc
      (∑ a, ∑ b, P.w a * (K a).w b) =
          ∑ a, P.w a * (∑ b, (K a).w b) := by
            congr 1
            funext a
            rw [Finset.mul_sum]
      _ = ∑ a, P.w a := by simp [FinLaw.sum_one]
      _ = 1 := P.sum_one

/-- Push a finite law forward along a map. -/
noncomputable def map {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) : FinLaw β where
  w b := ∑ a, if f a = b then P.w a else 0
  nonneg b := Finset.sum_nonneg fun a _ => by
    split_ifs with h
    · exact P.nonneg a
    · exact le_rfl
  sum_one := by
    classical
    rw [Finset.sum_comm]
    calc
      ∑ a, ∑ b, (if f a = b then P.w a else 0) = ∑ a, P.w a := by
        congr 1
        funext a
        simp
      _ = 1 := P.sum_one

/-- Conditioning on a positive-mass finite event. -/
noncomputable def cond (P : FinLaw Ω) (A : Finset Ω)
    (h : 0 < ∑ ω ∈ A, P.w ω) : FinLaw Ω where
  w ω := (if ω ∈ A then P.w ω else 0) / ∑ x ∈ A, P.w x
  nonneg ω := by
    apply div_nonneg
    · split_ifs with hmem
      · exact P.nonneg ω
      · exact le_rfl
    · exact h.le
  sum_one := by
    classical
    have hsum : (∑ ω, if ω ∈ A then P.w ω else 0) = ∑ ω ∈ A, P.w ω := by
      simp [Finset.sum_ite_mem, Finset.univ_inter]
    rw [← Finset.sum_div, hsum, div_self (ne_of_gt h)]

/-- Uniform law on a nonempty finite set. -/
noncomputable def uniform [DecidableEq Ω] (s : Finset Ω) (hs : s.Nonempty) : FinLaw Ω where
  w ω := if ω ∈ s then 1 / (s.card : ℝ) else 0
  nonneg ω := by split_ifs <;> positivity
  sum_one := by
    classical
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have hcard : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr hs).ne'
    field_simp

end FinLaw

/-- A real-valued function reads only coordinates indexed by `S`. -/
def DependsOn {ι : Type*} {Ω : ι → Type*} (F : (∀ i, Ω i) → ℝ) (S : Set ι) : Prop :=
  ∀ a b : (∀ i, Ω i), (∀ i ∈ S, a i = b i) → F a = F b

/-- Nonnegative test-function comparison on a specified coordinate scope. -/
def UpperComp {ι : Type*} {Ω : ι → Type*} [Fintype (∀ i, Ω i)]
    (P Q : FinLaw (∀ i, Ω i)) (S : Set ι) (c : ℝ) : Prop :=
  ∀ F : (∀ i, Ω i) → ℝ, (∀ ω, 0 ≤ F ω) → DependsOn F S → P.E F ≤ c * Q.E F

/-- A Boolean cube position of dimension `n`. -/
abbrev CubePos (n : ℕ) := Fin n → Bool

/-- Flip one coordinate of a cube position. -/
def flipPos {n : ℕ} (v : CubePos n) (j : Fin n) : CubePos n := Function.update v j (!v j)

/-- Hamming ball around a cube position. -/
def cubeBall {n : ℕ} (v : CubePos n) (r : ℕ) : Finset (CubePos n) :=
  Finset.univ.filter fun w => hammingDist v w ≤ r

/-- Prefix leaf with prefix word `w` and length `ell`. -/
def prefixLeaf {n : ℕ} (ell : ℕ) (w : CubePos n) : Set (CubePos n) :=
  {v | ∀ j : Fin n, j.val < ell → v j = w j}

/-- The top `h` coordinates, used as the nested internal-coordinate set. -/
def topCoordinates (n h : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => n - h ≤ j.val

/-- A cube slice fixes all coordinates outside `I`. -/
def cubeSlice {n : ℕ} (I : Finset (Fin n)) (v : CubePos n) : Set (CubePos n) :=
  {w | ∀ j, j ∉ I → w j = v j}

/-- A monochromatic cross-cube occurs in the stage colouring at index `k`. -/
def CubeIn (T : Stage) (k : ℕ) (c : Colour) : Prop :=
  Nonempty ((OAI.HypercubeRamsey.cube (T.S.n k)).Copy
    (OAI.HypercubeRamsey.crossGraph (Hits (T.S.E k) c)))

/-- Part C's complete explicit-weight uniform law on a nonempty host subset. -/
noncomputable def Law.unifCore {N : ℕ} (A : Finset (Fin N)) (hA : A.Nonempty) : Law N where
  w x := if x ∈ A then (A.card : ℝ)⁻¹ else 0
  nonneg x := by split_ifs <;> positivity
  sum_eq_one := by
    classical
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have hcard : (A.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr hA).ne'
    field_simp

end HypercubeRamsey
