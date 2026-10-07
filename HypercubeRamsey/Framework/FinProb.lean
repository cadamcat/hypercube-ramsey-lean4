import Mathlib

/-!
# Finite probability

Every random object in the paper is finite: a law is a nonnegative weight function with total mass one on a
finite type. Expectations are finite sums; conditional expectations are ratios (zero on a null event).
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- A probability law on a finite type. -/
structure FinProb (Ω : Type*) [Fintype Ω] where
  w : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ w ω
  sum_eq_one : ∑ ω, w ω = 1

namespace FinProb

variable {Ω : Type*} [Fintype Ω]

noncomputable def expect (P : FinProb Ω) (f : Ω → ℝ) : ℝ := ∑ ω, P.w ω * f ω

open Classical in
noncomputable def pr (P : FinProb Ω) (A : Ω → Prop) : ℝ := ∑ ω, if A ω then P.w ω else 0

open Classical in
/-- `E[f | A]`, zero when `P(A) = 0`. -/
noncomputable def condExp (P : FinProb Ω) (f : Ω → ℝ) (A : Ω → Prop) : ℝ :=
  P.expect (fun ω => (if A ω then 1 else 0) * f ω) / P.pr A

/-- Product law. -/
noncomputable def pi {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) : FinProb (∀ i, Ω i) where
  w ω := ∏ i, (P i).w (ω i)
  nonneg ω := Finset.prod_nonneg fun i _ => (P i).nonneg (ω i)
  sum_eq_one := by
    rw [← Fintype.prod_sum]
    simp [FinProb.sum_eq_one]

/-- Sequential sampling: draw `a` from `P`, then `b` from `K a`. -/
noncomputable def bind {α β : Type*} [Fintype α] [Fintype β] (P : FinProb α) (K : α → FinProb β) :
    FinProb (α × β) where
  w ab := P.w ab.1 * (K ab.1).w ab.2
  nonneg ab := mul_nonneg (P.nonneg _) ((K _).nonneg _)
  sum_eq_one := sorry

/-- Image law. -/
noncomputable def map {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (P : FinProb α) (f : α → β) :
    FinProb β where
  w b := ∑ a, if f a = b then P.w a else 0
  nonneg b := Finset.sum_nonneg fun a _ => by split_ifs <;> simp [P.nonneg a]
  sum_eq_one := sorry

open Classical in
/-- Conditioning on an event of positive probability. -/
noncomputable def cond (P : FinProb Ω) (A : Ω → Prop) (h : 0 < P.pr A) : FinProb Ω where
  w ω := (if A ω then P.w ω else 0) / P.pr A
  nonneg ω := div_nonneg (by split_ifs <;> simp [P.nonneg ω]) h.le
  sum_eq_one := sorry

/-- Uniform law on a nonempty finite set. -/
noncomputable def uniform [DecidableEq Ω] (s : Finset Ω) (h : s.Nonempty) : FinProb Ω where
  w ω := if ω ∈ s then (s.card : ℝ)⁻¹ else 0
  nonneg ω := by split_ifs <;> simp
  sum_eq_one := sorry

/-- `f` depends only on the coordinates in `s`. -/
def DependsOn {ι : Type*} {Ω : ι → Type*} {β : Sort*} (f : (∀ i, Ω i) → β) (s : Finset ι) : Prop :=
  ∀ ω ω', (∀ i ∈ s, ω i = ω' i) → f ω = f ω'

end FinProb

end HypercubeRamsey
