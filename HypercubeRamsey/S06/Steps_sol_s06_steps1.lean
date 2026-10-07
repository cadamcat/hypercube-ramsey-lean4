import HypercubeRamsey.S06.Defs
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.S06.Lane_sol_s06_steps1

open OAI.HypercubeRamsey Classical
open scoped BigOperators

noncomputable section

theorem ratio_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ safeRatio6 a b := by
  unfold safeRatio6
  split_ifs <;> simp [div_nonneg ha hb]

/-- Changing unused independent coordinates preserves an expectation. -/
theorem pi_expect_congr_on {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (P Q : I → FinProb Ω) (S : Finset I) (f : (I → Ω) → ℝ) (z₀ : I → Ω)
    (hf : FinProb.DependsOn f S) (hPQ : ∀ i ∈ S, P i = Q i) :
    (FinProb.pi P).expect f = (FinProb.pi Q).expect f := by
  rw [FinProb.pi_expect_depends P S f z₀ hf, FinProb.pi_expect_depends Q S f z₀ hf]
  congr 1
  congr 1
  funext i
  exact hPQ i.1 i.2

/-- Expose one coordinate of an independent product. -/
theorem pi_expect_split_at {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (P : I → FinProb Ω) (k : I) (f : (I → Ω) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ J : ({j : I // j ≠ k} → Ω),
        (FinProb.pi (fun j : {j : I // j ≠ k} => P j.1)).w J *
          ∑ i, (P k).w i * f ((Equiv.funSplitAt k Ω).symm (i, J)) := by
  let e := Equiv.funSplitAt k Ω
  have hw (z : I → Ω) : (FinProb.pi P).w z =
      (P k).w (z k) * (FinProb.pi (fun j : {j : I // j ≠ k} => P j.1)).w
        (fun j => z j.1) := by
    letI : Fintype {j : I // j = k} := Subtype.fintype (fun j => j = k)
    change (∏ j, (P j).w (z j)) = _
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun j : I => j = k)]
    have hsingle : (∏ j : {j : I // j = k}, (P j.1).w (z j.1)) = (P k).w (z k) := by
      apply Finset.prod_eq_single (⟨k, rfl⟩ : {j : I // j = k})
      · intro j _ hj
        exact (hj (Subtype.ext j.property)).elim
      · intro h
        exact (h (Finset.mem_univ _)).elim
    rw [hsingle]
    rfl
  unfold FinProb.expect
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hw]
  have hoff : (fun j : {j : I // j ≠ k} => e.symm (i,J) j.1) = J := by
    funext j
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt, j.property]
  rw [hoff]
  have hat : e.symm (i,J) k = i := by simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
  rw [hat]
  ring

def density {I Ω T : Type*} [Fintype I] [Fintype Ω] [Fintype T]
    (P : FinProb T) (Q : T → I → FinProb Ω) (R : I → FinProb Ω)
    (gate : T → Prop) (S : Finset I) (z : I → Ω) : ℝ :=
  ∑ i, P.w i * (if gate i then 1 else 0) *
    ∏ ℓ ∈ S, safeRatio6 ((Q i ℓ).w (z ℓ)) ((R ℓ).w (z ℓ))

theorem density_nonneg {I Ω T : Type*} [Fintype I] [Fintype Ω] [Fintype T]
    (P : FinProb T) (Q : T → I → FinProb Ω) (R : I → FinProb Ω)
    (gate : T → Prop) (S : Finset I) (z : I → Ω) : 0 ≤ density P Q R gate S z := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · apply mul_nonneg (P.nonneg i)
    split_ifs <;> norm_num
  · exact Finset.prod_nonneg fun ℓ _ => ratio_nonneg
      ((Q i ℓ).nonneg _) ((R ℓ).nonneg _)

set_option maxHeartbeats 600000 in
/-- Every product of likelihood ratios integrates to at most one. -/
theorem ratio_product_integral_le_one {I Ω : Type*}
    [Fintype I] [DecidableEq I] [Fintype Ω] (Q R : I → FinProb Ω) (S : Finset I) :
    (FinProb.pi R).expect (fun z =>
      ∏ ℓ ∈ S, safeRatio6 ((Q ℓ).w (z ℓ)) ((R ℓ).w (z ℓ))) ≤ 1 := by
  have hr (ℓ : I) (y : Ω) :
      (R ℓ).w y * safeRatio6 ((Q ℓ).w y) ((R ℓ).w y) ≤ (Q ℓ).w y := by
    by_cases h : (R ℓ).w y = 0
    · simp [h, safeRatio6, (Q ℓ).nonneg y]
    · simp [safeRatio6, h, mul_div_cancel₀]
  have hsum (ℓ : I) : (∑ y, (R ℓ).w y *
      (if ℓ ∈ S then safeRatio6 ((Q ℓ).w y) ((R ℓ).w y) else 1)) ≤ 1 := by
    by_cases hℓ : ℓ ∈ S
    · simp only [hℓ, if_true]
      exact le_trans (Finset.sum_le_sum fun y _ => hr ℓ y) (le_of_eq (Q ℓ).sum_eq_one)
    · simp [hℓ, (R ℓ).sum_eq_one]
  calc
    _ = ∑ z : I → Ω, ∏ ℓ, (R ℓ).w (z ℓ) *
        (if ℓ ∈ S then safeRatio6 ((Q ℓ).w (z ℓ)) ((R ℓ).w (z ℓ)) else 1) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro z _
      change (∏ ℓ, (R ℓ).w (z ℓ)) *
        (∏ ℓ ∈ S, safeRatio6 ((Q ℓ).w (z ℓ)) ((R ℓ).w (z ℓ))) = _
      rw [← Fintype.prod_ite_mem S]
      exact (Finset.prod_mul_distrib).symm
    _ = ∏ ℓ, ∑ y, (R ℓ).w y *
        (if ℓ ∈ S then safeRatio6 ((Q ℓ).w y) ((R ℓ).w y) else 1) :=
      (Fintype.prod_sum (fun ℓ y => (R ℓ).w y *
        (if ℓ ∈ S then safeRatio6 ((Q ℓ).w y) ((R ℓ).w y) else 1))).symm
    _ ≤ ∏ _ℓ : I, (1 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro ℓ _
        apply Finset.sum_nonneg
        intro y _
        apply mul_nonneg ((R ℓ).nonneg y)
        split_ifs
        · exact ratio_nonneg ((Q ℓ).nonneg y) ((R ℓ).nonneg y)
        · norm_num
      · exact fun ℓ _ => hsum ℓ
    _ = 1 := by simp

theorem density_integral_le_one {I Ω T : Type*}
    [Fintype I] [DecidableEq I] [Fintype Ω] [Fintype T]
    (P : FinProb T) (Q : T → I → FinProb Ω) (R : I → FinProb Ω)
    (gate : T → Prop) (S : Finset I) :
    (FinProb.pi R).expect (density P Q R gate S) ≤ 1 := by
  unfold density FinProb.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, (P.w i * (if gate i then 1 else 0)) *
        (FinProb.pi R).expect (fun z =>
          ∏ ℓ ∈ S, safeRatio6 ((Q i ℓ).w (z ℓ)) ((R ℓ).w (z ℓ))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [FinProb.expect, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ ∑ i, P.w i := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hg : gate i
      · simp only [hg, if_true, mul_one]
        simpa using mul_le_mul_of_nonneg_left (ratio_product_integral_le_one (Q i) R S)
          (P.nonneg i)
      · simp [hg, P.nonneg i]
    _ = 1 := P.sum_eq_one

/-- Conditional true-gated mass agrees with its density against the deleted product. -/
theorem gated_expect_density {I Ω T : Type*}
    [Fintype I] [DecidableEq I] [Fintype Ω] [Fintype T]
    (P : FinProb T) (Q : T → I → FinProb Ω) (R : I → FinProb Ω)
    (gate : T → Prop) (S : Finset I) (A : (I → Ω) → Prop) (z₀ : I → Ω)
    (hA : FinProb.DependsOn (fun z => if A z then (1 : ℝ) else 0) S)
    (habs : ∀ i, gate i → ∀ ℓ ∈ S, ∀ y, (R ℓ).w y = 0 → (Q i ℓ).w y = 0) :
    (∑ i, P.w i * (if gate i then (FinProb.pi (Q i)).pr A else 0)) =
      (FinProb.pi R).expect (fun z => if A z then density P Q R gate S z else 0) := by
  let Q' (i : T) (ℓ : I) := if ℓ ∈ S then Q i ℓ else R ℓ
  have hchange (i : T) : (FinProb.pi (Q i)).pr A = (FinProb.pi (Q' i)).pr A := by
    have h := pi_expect_congr_on (Q i) (Q' i) S
      (fun z => if A z then (1 : ℝ) else 0) z₀ hA (fun ℓ hℓ => by simp [Q', hℓ])
    simpa [FinProb.expect, FinProb.pr] using h
  have hw (i : T) (hg : gate i) (z : I → Ω) :
      (FinProb.pi (Q' i)).w z = (FinProb.pi R).w z *
        ∏ ℓ ∈ S, safeRatio6 ((Q i ℓ).w (z ℓ)) ((R ℓ).w (z ℓ)) := by
    rw [← Fintype.prod_ite_mem S]
    change (∏ ℓ, (Q' i ℓ).w (z ℓ)) =
      (∏ ℓ, (R ℓ).w (z ℓ)) *
        ∏ ℓ, if ℓ ∈ S then safeRatio6 ((Q i ℓ).w (z ℓ)) ((R ℓ).w (z ℓ)) else 1
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ℓ _
    by_cases hℓ : ℓ ∈ S
    · simp only [Q', hℓ, if_true]
      by_cases hz : (R ℓ).w (z ℓ) = 0
      · simp [hz, habs i hg ℓ hℓ (z ℓ) hz, safeRatio6]
      · simp [safeRatio6, hz, mul_div_cancel₀]
    · simp [Q', hℓ]
  have hterm (i : T) : P.w i * (if gate i then (FinProb.pi (Q i)).pr A else 0) =
      ∑ z, if gate i ∧ A z then P.w i * (FinProb.pi (Q' i)).w z else 0 := by
    rw [hchange]
    by_cases hg : gate i <;> simp [FinProb.pr, hg, Finset.mul_sum, mul_ite]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro z _
  by_cases ha : A z
  · simp only [ha, and_true, if_pos]
    unfold density
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hg : gate i
    · simp [hg, hw i hg, mul_assoc, mul_comm, mul_left_comm]
    · simp [hg]
  · simp [ha]



theorem density_depends {I Ω T : Type*} [Fintype I] [Fintype Ω] [Fintype T]
    (P : FinProb T) (Q : T → I → FinProb Ω) (R : I → FinProb Ω)
    (gate : T → Prop) (S : Finset I) : FinProb.DependsOn (density P Q R gate S) S := by
  intro z z' hz
  unfold density
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  rw [hz ℓ hℓ]

/-- The conditional Step 2 union bound, before averaging over the retained base. -/
theorem gated_tests_bound {I Ω T : Type*}
    [Fintype I] [DecidableEq I] [Fintype Ω] [Fintype T]
    (P : FinProb T) (Q : T → I → FinProb Ω) (R : I → FinProb Ω)
    (gate : T → Prop) (S : Finset I) (a : ℝ) (ha : 0 ≤ a) (z₀ : I → Ω)
    (habs : ∀ i, gate i → ∀ ℓ ∈ S, ∀ y, (R ℓ).w y = 0 → (Q i ℓ).w y = 0) :
    (∑ i, P.w i * (if gate i then (FinProb.pi (Q i)).pr (fun z =>
      density P Q R gate S z < a ∨ ∃ ℓ ∈ S,
        density P Q R gate S z < a * density P Q R gate (S.erase ℓ) z) else 0)) ≤
      ((S.card : ℝ) + 1) * a := by
  classical
  let m := density P Q R gate S
  let d (ℓ : I) := density P Q R gate (S.erase ℓ)
  let A (z : I → Ω) := m z < a ∨ ∃ ℓ ∈ S, m z < a * d ℓ z
  letI : DecidablePred A := fun z => Classical.propDecidable (A z)
  have hA : FinProb.DependsOn (fun z => @ite ℝ (A z) (Classical.propDecidable (A z)) 1 0) S := by
    intro z z' hz
    have hm := density_depends P Q R gate S z z' hz
    have hd (ℓ : I) : d ℓ z = d ℓ z' :=
      density_depends P Q R gate (S.erase ℓ) z z' (fun j hj => hz j (Finset.mem_of_mem_erase hj))
    simp only [A, m, hm, hd]
  rw [gated_expect_density P Q R gate S A z₀ hA habs]
  let low (z : I → Ω) := if m z < a then m z else 0
  let ratio (ℓ : I) (z : I → Ω) := if m z < a * d ℓ z then m z else 0
  have hm0 (z) : 0 ≤ m z := density_nonneg P Q R gate S z
  have hr0 (ℓ) (z) : 0 ≤ ratio ℓ z := by dsimp [ratio]; split_ifs <;> simp [hm0]
  have hpoint (z) : (if A z then m z else 0) ≤ low z + ∑ ℓ ∈ S, ratio ℓ z := by
    by_cases hl : m z < a
    · have hsum0 := Finset.sum_nonneg (fun ℓ _ => hr0 ℓ z) (s := S)
      simp only [A, hl, true_or, if_true, low]
      linarith
    · simp only [low, hl, if_false, zero_add]
      by_cases hb : ∃ ℓ ∈ S, m z < a * d ℓ z
      · have hb' := hb
        obtain ⟨ℓ, hℓ, hbad⟩ := hb
        simpa [A, hl, hb', ratio, hbad] using
          (Finset.single_le_sum (fun j _ => hr0 j z) hℓ)
      · simp [A, hl, hb]
        exact Finset.sum_nonneg fun ℓ _ => hr0 ℓ z
  have hlow : (FinProb.pi R).expect low ≤ a := by
    calc
      _ ≤ (FinProb.pi R).expect (fun _ => a) := FinProb.expect_mono _ (fun z => by
        dsimp [low]; split_ifs <;> [exact le_of_lt ‹m z < a›; exact ha])
      _ = a := FinProb.expect_const _ a
  have hratio (ℓ) : (FinProb.pi R).expect (ratio ℓ) ≤ a := by
    calc
      _ ≤ (FinProb.pi R).expect (fun z => a * d ℓ z) := FinProb.expect_mono _ (fun z => by
        dsimp [ratio]
        split_ifs with h
        · exact le_of_lt h
        · exact mul_nonneg ha (density_nonneg P Q R gate (S.erase ℓ) z))
      _ = a * (FinProb.pi R).expect (d ℓ) := FinProb.expect_smul _ _ _
      _ ≤ a * 1 := mul_le_mul_of_nonneg_left (density_integral_le_one P Q R gate (S.erase ℓ)) ha
      _ = a := mul_one a
  calc
    _ ≤ (FinProb.pi R).expect (fun z => low z + ∑ ℓ ∈ S, ratio ℓ z) :=
      FinProb.expect_mono _ hpoint
    _ = (FinProb.pi R).expect low + ∑ ℓ ∈ S, (FinProb.pi R).expect (ratio ℓ) := by
      rw [FinProb.expect_add]
      congr 1
      unfold FinProb.expect
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ a + ∑ _ℓ ∈ S, a := add_le_add hlow (Finset.sum_le_sum fun ℓ _ => hratio ℓ)
    _ = ((S.card : ℝ) + 1) * a := by simp; ring

end
end HypercubeRamsey.S06.Lane_sol_s06_steps1
