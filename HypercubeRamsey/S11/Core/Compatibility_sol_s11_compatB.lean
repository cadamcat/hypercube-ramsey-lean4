import HypercubeRamsey.S11.Core.Definitions
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.Lane_sol_s11_compatB

open HypercubeRamsey OAI.HypercubeRamsey
open scoped BigOperators

/-- A disjoint packing that retains half a sample is dominated by its coordinate counts. -/
theorem packing_average_le {r N : ℕ} (s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (z : Fin r → Fin N) (hz : Function.Injective z)
    (P : Finset (Finset (Fin r))) (hP : P.Nonempty)
    (hdisj : ∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D)
    (hdenom : (r : ℝ) / 2 < (P.card : ℝ) * (s : ℝ))
    (D : Finset (Fin r) → Law N)
    (hD : ∀ C ∈ P, ∀ y, (D C).w y = if y ∈ C.image z then (s : ℝ)⁻¹ else 0)
    (a : ℝ) (ha : 0 ≤ a) (y : Fin N) :
    (∑ C : Finset (Fin r),
      (a * (if C ∈ P then (P.card : ℝ)⁻¹ else 0)) * (D C).w y) ≤
      (a * (2 / (r : ℝ))) * (∑ j : Fin r, if z j = y then (1 : ℝ) else 0) := by
  classical
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hPpos : 0 < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hP
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hfactor : (P.card : ℝ)⁻¹ * (s : ℝ)⁻¹ ≤ 2 / (r : ℝ) := by
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (r : ℝ) / 2) hdenom.le
    calc
      (P.card : ℝ)⁻¹ * (s : ℝ)⁻¹ = 1 / ((P.card : ℝ) * (s : ℝ)) := by
        rw [one_div, mul_inv_rev, mul_comm]
      _ ≤ 1 / ((r : ℝ) / 2) := h
      _ = 2 / (r : ℝ) := by field_simp
  have hunique : ∀ C ∈ P, ∀ D ∈ P, y ∈ C.image z → y ∈ D.image z → C = D := by
    intro C hC D hD hyC hyD
    obtain ⟨j, hjC, hjy⟩ := Finset.mem_image.mp hyC
    obtain ⟨k, hkD, hky⟩ := Finset.mem_image.mp hyD
    have hjk : j = k := hz (hjy.trans hky.symm)
    subst k
    by_contra hCD
    exact (Finset.disjoint_left.mp (hdisj C hC D hD hCD)) hjC hkD
  let T := P.filter (fun C => y ∈ C.image z)
  have hTcard : T.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro C hC D hD
    exact hunique C (Finset.mem_filter.mp hC).1 D (Finset.mem_filter.mp hD).1
      (Finset.mem_filter.mp hC).2 (Finset.mem_filter.mp hD).2
  have hcount :
      (∑ C : Finset (Fin r), if C ∈ P then if y ∈ C.image z then (1 : ℝ) else 0 else 0) ≤ 1 := by
    have hsum :
        (∑ C : Finset (Fin r), if C ∈ P then if y ∈ C.image z then (1 : ℝ) else 0 else 0) =
          (T.card : ℝ) := by
      simp [T, Finset.sum_ite_mem_eq, Finset.sum_filter]
    rw [hsum]
    exact_mod_cast hTcard
  have hmass :
      (∑ C : Finset (Fin r), (a * (if C ∈ P then (P.card : ℝ)⁻¹ else 0)) * (D C).w y) ≤
        a * (2 / (r : ℝ)) := by
    have heq :
        (∑ C : Finset (Fin r), (a * (if C ∈ P then (P.card : ℝ)⁻¹ else 0)) * (D C).w y) =
          (a * ((P.card : ℝ)⁻¹ * (s : ℝ)⁻¹)) *
            (∑ C : Finset (Fin r), if C ∈ P then if y ∈ C.image z then (1 : ℝ) else 0 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro C _
      by_cases hC : C ∈ P
      · rw [hD C hC y]
        by_cases hy : y ∈ C.image z <;> simp [hC, hy] <;> ring
      · simp [hC]
    rw [heq]
    calc
      _ ≤ a * ((P.card : ℝ)⁻¹ * (s : ℝ)⁻¹) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hcount
          (mul_nonneg ha (mul_nonneg (inv_nonneg.mpr hPpos.le) (inv_nonneg.mpr hsR.le)))
      _ ≤ a * (2 / (r : ℝ)) := mul_le_mul_of_nonneg_left hfactor ha
  by_cases hcoord : ∃ j : Fin r, z j = y
  · obtain ⟨j, hj⟩ := hcoord
    have hcoords : 1 ≤ ∑ k : Fin r, if z k = y then (1 : ℝ) else 0 := by
      calc
        1 = (if z j = y then (1 : ℝ) else 0) := by simp [hj]
        _ ≤ ∑ k : Fin r, if z k = y then (1 : ℝ) else 0 :=
          Finset.single_le_sum (f := fun k : Fin r => if z k = y then (1 : ℝ) else 0)
            (fun k _ => by positivity) (Finset.mem_univ j)
    exact hmass.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hcoords
        (mul_nonneg ha (div_nonneg (by norm_num) hrR.le)))
  · have hzero :
        (∑ C : Finset (Fin r), (a * (if C ∈ P then (P.card : ℝ)⁻¹ else 0)) * (D C).w y) = 0 := by
      apply Finset.sum_eq_zero
      intro C _
      by_cases hC : C ∈ P
      · have hnot : y ∉ C.image z := by
          intro hy
          obtain ⟨j, _, hjy⟩ := Finset.mem_image.mp hy
          exact hcoord ⟨j, hjy⟩
        rw [hD C hC y, if_neg hnot, mul_zero]
      · simp [hC]
    have hneq (j : Fin r) : z j ≠ y := fun hj => hcoord ⟨j, hj⟩
    rw [hzero]
    simp only [hneq, if_false, Finset.sum_const_zero, mul_zero, le_refl]

/-- Average the coordinate domination of a retained sample over its conditional law. -/
theorem sample_average_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (r : ℕ) (hr : 0 < r) (P : FinProb α)
    (Q : α → FinProb (Fin r → β)) (ρ : α → β → ℝ)
    (hcoord : ∀ a j b, (Q a).expect (fun z => if z j = b then (1 : ℝ) else 0) ≤ 2 * ρ a b)
    (b : β) :
    (∑ q : α × (Fin r → β), (FinProb.bind P Q).w q * (2 / (r : ℝ)) *
      (∑ j : Fin r, if q.2 j = b then (1 : ℝ) else 0)) ≤
      4 * ∑ a, P.w a * ρ a b := by
  classical
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hrow (a : α) :
      (Q a).expect (fun z => ∑ j : Fin r, if z j = b then (1 : ℝ) else 0) ≤
        (r : ℝ) * (2 * ρ a b) := by
    calc
      _ = ∑ j : Fin r, (Q a).expect (fun z => if z j = b then (1 : ℝ) else 0) := by
        unfold FinProb.expect
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ ≤ ∑ j : Fin r, 2 * ρ a b := Finset.sum_le_sum fun j _ => hcoord a j b
      _ = (r : ℝ) * (2 * ρ a b) := by simp
  have hrowScale (a : α) :
      (Q a).expect (fun z => (2 / (r : ℝ)) *
        (∑ j : Fin r, if z j = b then (1 : ℝ) else 0)) ≤ 4 * ρ a b := by
    rw [FinProb.expect_smul]
    calc
      _ ≤ (2 / (r : ℝ)) * ((r : ℝ) * (2 * ρ a b)) :=
        mul_le_mul_of_nonneg_left (hrow a) (by positivity)
      _ = 4 * ρ a b := by field_simp; ring
  calc
    _ = (FinProb.bind P Q).expect (fun q => (2 / (r : ℝ)) *
        (∑ j : Fin r, if q.2 j = b then (1 : ℝ) else 0)) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = ∑ a, P.w a * (Q a).expect (fun z => (2 / (r : ℝ)) *
        (∑ j : Fin r, if z j = b then (1 : ℝ) else 0)) :=
      FinProb.bind_expect P Q (fun _ z => (2 / (r : ℝ)) *
        (∑ j : Fin r, if z j = b then (1 : ℝ) else 0))
    _ ≤ ∑ a, P.w a * (4 * ρ a b) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hrowScale a) (P.nonneg a)
    _ = 4 * ∑ a, P.w a * ρ a b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- Restriction to a subtype cannot increase a nonnegative finite sum. -/
theorem subtype_sum_le {α : Type} [Fintype α] (S : Finset α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) : (∑ a : {a // a ∈ S}, f a.1) ≤ ∑ a, f a := by
  classical
  have hUniv : (Finset.univ : Finset {a // a ∈ S}) =
      Finset.subtype (fun a : α => a ∈ S) (Finset.univ : Finset α) := by
    ext a
    simp
  rw [hUniv, Finset.sum_subtype_eq_sum_filter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun a _ _ => hf a)

/-- Reindex a finite probability family into the natural cluster indexing. -/
theorem cluster_of_finprob {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {G : Colour} {ζ δ : ℝ}
    {α : Type} [Fintype α] (μ : Law N) (P : FinProb α) (D : α → Law N)
    (hμ : μ.SupportedIn X) (hD : ∀ a, (D a).SupportedIn Y)
    (hwidth : μ.WidthLE ((n : ℝ) ^ δ))
    (hagg : ∀ y, ∑ a, P.w a * (D a).w y ≤ Real.exp ((n : ℝ) ^ δ) / N)
    (hatom : ∀ a y, (D a).w y ≤ Real.exp (-((n : ℝ) ^ ζ)))
    (hpair : ∀ a, 0 < P.w a → ∀ y y', 0 < (D a).w y → 0 < (D a).w y' →
      1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G μ y y') :
    PCluster G ζ δ n N E (X, Y) := by
  classical
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  have hsum (f : α → ℝ) : (∑ j, f (e j)) = ∑ a, f a :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  refine ⟨μ, Fintype.card α, (fun j => P.w (e j)), (fun j => D (e j)),
    hμ, (fun j => hD (e j)), (fun j => P.nonneg (e j)), ?_, hwidth, ?_,
    (fun j y => hatom (e j) y), (fun j => hpair (e j))⟩
  · exact (hsum P.w).trans P.sum_eq_one
  · intro y
    rw [hsum (fun a => P.w a * (D a).w y)]
    exact hagg y

end HypercubeRamsey.Lane_sol_s11_compatB
