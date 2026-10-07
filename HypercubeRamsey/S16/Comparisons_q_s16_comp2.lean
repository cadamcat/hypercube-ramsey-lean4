import HypercubeRamsey.PartC.Core

/-! Helpers owned by lane q-s16-comp2. -/

namespace HypercubeRamsey.S16.Lane_q_s16_comp2

open Classical
open scoped BigOperators

/-- A product test on a product law factors into its coordinate expectations. -/
theorem pi_expect_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (f : ∀ i, Ω i → ℝ) :
    (FinLaw.pi P).E (fun x => ∏ i, f i (x i)) =
      ∏ i, (P i).E (f i) := by
  classical
  simp only [FinLaw.E, FinLaw.pi]
  have hprod (g h : ∀ i, Ω i → ℝ) (ω : ∀ i, Ω i) :
      (∏ i, g i (ω i)) * ∏ i, h i (ω i) = ∏ i, g i (ω i) * h i (ω i) := by
    rw [← Finset.prod_mul_distrib]
  calc
    (∑ ω : (∀ i, Ω i), (∏ i, (P i).w (ω i)) * ∏ i, f i (ω i)) =
        ∑ ω : (∀ i, Ω i), ∏ i, (P i).w (ω i) * f i (ω i) := by
          apply Finset.sum_congr rfl
          intro ω hω
          exact hprod (fun i z => (P i).w z) f ω
    _ = ∏ i, ∑ z : Ω i, (P i).w z * f i z := by
          simpa using (Fintype.prod_sum
            (fun i z => (P i).w z * f i z)).symm

/-- A finite product law assigns a cylinder the product of its coordinate atom weights. -/
theorem pi_pr_cylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (S : Finset ι) (x : ∀ i, Ω i) :
    (FinLaw.pi P).pr (fun ω => ∀ i ∈ S, ω i = x i) =
      ∏ i ∈ S, (P i).w (x i) := by
  classical
  let f : ∀ i, Ω i → ℝ := fun i z =>
    if i ∈ S then if z = x i then 1 else 0 else 1
  have hindicator (ω : ∀ i, Ω i) :
      (if ∀ i ∈ S, ω i = x i then (1 : ℝ) else 0) = ∏ i, f i (ω i) := by
    by_cases h : ∀ i ∈ S, ω i = x i
    · simp only [if_pos h]
      rw [Finset.prod_ite_mem_eq]
      symm
      apply Finset.prod_eq_one
      intro i hi
      simp [f, hi, h i hi]
    · have hex : ∃ i, i ∈ S ∧ ω i ≠ x i := by
        by_contra hn
        apply h
        intro i hi
        by_contra hix
        exact hn ⟨i, hi, hix⟩
      obtain ⟨i, hiS, hix⟩ := hex
      have hz : (∏ j, f j (ω j)) = 0 := by
        rw [Finset.prod_ite_mem_eq]
        exact Finset.prod_eq_zero hiS (by simp [f, hiS, hix])
      simp [h, hz]
  calc
    (FinLaw.pi P).pr (fun ω => ∀ i ∈ S, ω i = x i) =
        (FinLaw.pi P).E (fun ω => if ∀ i ∈ S, ω i = x i then 1 else 0) := by
          simp only [FinLaw.pr, FinLaw.E, FinLaw.pi]
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases h : ∀ i ∈ S, ω i = x i <;> simp [h]
    _ = (FinLaw.pi P).E (fun ω => ∏ i, f i (ω i)) := by
          congr 1
          funext ω
          exact hindicator ω
    _ = ∏ i, (P i).E (f i) := pi_expect_prod P f
    _ = ∏ i ∈ S, (P i).w (x i) := by
          have hcoord (i : ι) : (P i).E (f i) =
              if i ∈ S then (P i).w (x i) else 1 := by
            by_cases hi : i ∈ S
            · simp [f, hi, FinLaw.E]
            · simp [f, hi, FinLaw.E, FinLaw.sum_one]
          rw [show (fun i => (P i).E (f i)) =
            (fun i => if i ∈ S then (P i).w (x i) else 1) from funext hcoord]
          exact Finset.prod_ite_mem_eq S (fun i => (P i).w (x i))

/-- The probability of a finite union is at most the sum of the probabilities. -/
theorem pr_exists_le_sum {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (P : FinLaw Ω) (A : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i, A i ω) ≤ ∑ i, P.pr (A i) := by
  classical
  letI : DecidablePred (fun ω => ∃ i, A i ω) := fun ω => Classical.propDecidable _
  letI : ∀ i, DecidablePred (A i) := fun i ω => Classical.propDecidable _
  unfold FinLaw.pr
  calc
    (∑ ω, if ∃ i, A i ω then P.w ω else 0) ≤
        ∑ ω, P.w ω * (∑ i, if A i ω then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro ω hω
          by_cases hex : ∃ i, A i ω
          · have hex' := hex
            obtain ⟨i, hi⟩ := hex
            have hone : (1 : ℝ) ≤ ∑ j, if A j ω then (1 : ℝ) else 0 := by
              calc
                1 = (if A i ω then (1 : ℝ) else 0) := by simp [hi]
                _ ≤ ∑ j, if A j ω then (1 : ℝ) else 0 :=
                  Finset.single_le_sum
                    (f := fun j => if A j ω then (1 : ℝ) else 0) (a := i)
                    (fun j hj => by by_cases hA : A j ω <;> simp [hA])
                    (Finset.mem_univ i)
            simpa only [if_pos hex', mul_one] using
              mul_le_mul_of_nonneg_left hone (P.nonneg ω)
          · have hsum : 0 ≤ ∑ i, if A i ω then (1 : ℝ) else 0 :=
              Finset.sum_nonneg fun i _ => by
                by_cases hA : A i ω <;> simp [hA]
            simpa only [if_neg hex] using mul_nonneg (P.nonneg ω) hsum
    _ = ∑ i, P.pr (A i) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          simp [FinLaw.pr, mul_ite]

/-- Monotonicity of probability under event inclusion. -/
theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (A B : Ω → Prop) (h : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  letI : DecidablePred A := fun ω => Classical.propDecidable _
  letI : DecidablePred B := fun ω => Classical.propDecidable _
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB : B ω := h ω hA
    simp [hA, hB]
  · by_cases hB : B ω
    · rw [if_neg hA, if_pos hB]
      exact P.nonneg ω
    · simp [hA, hB]

/-- Pointwise comparison is preserved by expectation under a finite law. -/
theorem expect_le {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (f g : Ω → ℝ) (h : ∀ ω, f ω ≤ g ω) : P.E f ≤ P.E g := by
  classical
  unfold FinLaw.E
  apply Finset.sum_le_sum
  intro ω hω
  exact mul_le_mul_of_nonneg_left (h ω) (P.nonneg ω)

/-- A constant factor can be pulled out of a finite expectation. -/
theorem expect_const_mul {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (c : ℝ) (f : Ω → ℝ) : P.E (fun x => c * f x) = c * P.E f := by
  classical
  unfold FinLaw.E
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Expectations agree when the functions agree on every atom of nonzero mass. -/
theorem expect_congr_of_support {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (f g : Ω → ℝ) (h : ∀ ω, P.w ω ≠ 0 → f ω = g ω) : P.E f = P.E g := by
  classical
  unfold FinLaw.E
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hw : P.w ω = 0
  · simp [hw]
  · rw [h ω hw]

/-- Expectations over independent finite laws commute. -/
theorem expect_indep_comm {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : FinLaw β) (f : α → β → ℝ) :
    P.E (fun a => Q.E (fun b => f a b)) =
      Q.E (fun b => P.E (fun a => f a b)) := by
  classical
  unfold FinLaw.E
  calc
    (∑ a, P.w a * ∑ b, Q.w b * f a b) =
        ∑ a, ∑ b, P.w a * (Q.w b * f a b) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
    _ = ∑ b, ∑ a, Q.w b * (P.w a * f a b) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro a ha
          ring
    _ = ∑ b, Q.w b * ∑ a, P.w a * f a b := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]

/-- Expectation under a finite bind is an iterated expectation. -/
theorem bind_expect {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (f : α × β → ℝ) :
    (FinLaw.bind P K).E f = P.E (fun a => (K a).E (fun b => f (a, b))) := by
  classical
  unfold FinLaw.E FinLaw.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Event probabilities under a sequential finite draw are iterated probabilities. -/
theorem bind_pr {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (A : α × β → Prop) :
    (FinLaw.bind P K).pr A = P.E (fun a => (K a).pr (fun b => A (a, b))) := by
  classical
  unfold FinLaw.pr FinLaw.E FinLaw.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : A (a, b) <;> simp [h]

/-- Pushforward preserves expectations. -/
theorem map_expect {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (P : FinLaw Ω) (f : Ω → Ξ) (g : Ξ → ℝ) :
    (FinLaw.map P f).E g = P.E (fun ω => g (f ω)) := by
  classical
  unfold FinLaw.E FinLaw.map
  change (∑ x ∈ (Finset.univ : Finset Ξ),
      (∑ ω ∈ (Finset.univ : Finset Ω), if f ω = x then P.w ω else 0) * g x) =
    ∑ ω ∈ (Finset.univ : Finset Ω), P.w ω * g (f ω)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω hω
  simp [Finset.sum_ite_eq, mul_ite]

/-- A comparison of all projected atom masses compares every nonnegative projected test. -/
theorem expect_map_le {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (P : FinLaw Ω) (f : Ω → Ξ) (Q : FinLaw Ξ) (c : ℝ) (g : Ξ → ℝ)
    (hg : ∀ x, 0 ≤ g x)
    (h : ∀ x, P.pr (fun ω => f ω = x) ≤ c * Q.w x) :
    P.E (fun ω => g (f ω)) ≤ c * Q.E g := by
  classical
  rw [← map_expect P f g]
  unfold FinLaw.E
  calc
    (∑ x, (FinLaw.map P f).w x * g x) ≤
        ∑ x, (c * Q.w x) * g x := by
          apply Finset.sum_le_sum
          intro x hx
          have hmap : (FinLaw.map P f).w x = P.pr (fun ω => f ω = x) := by
            unfold FinLaw.map FinLaw.pr
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases heq : f ω = x <;> simp [heq]
          rw [hmap]
          exact mul_le_mul_of_nonneg_right (h x) (hg x)
    _ = ∑ x, c * (Q.w x * g x) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = c * ∑ x, Q.w x * g x := by
          rw [Finset.mul_sum]

/-- A finite law can only live on a nonempty finite type. -/
theorem nonempty_of_finLaw {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) : Nonempty Ω := by
  classical
  by_contra h
  letI : IsEmpty Ω := ⟨fun ω => h ⟨ω⟩⟩
  have hzero : (∑ ω, P.w ω) = 0 := by simp
  rw [P.sum_one] at hzero
  norm_num at hzero

/-- A finite product law induces the corresponding product law on a coordinate subtype. -/
theorem pi_pr_subtype_cylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (S : Finset ι)
    (z : ∀ i : {i // i ∈ S}, Ω i.1) :
    (FinLaw.pi P).pr (fun ω => ∀ (i : ι) (hi : i ∈ S), ω i = z ⟨i, hi⟩) =
      ∏ i : {i // i ∈ S}, (P i.1).w (z i) := by
  classical
  letI scopeFintype : Fintype {i // i ∈ S} := Fintype.ofFinset S (fun _ => Iff.rfl)
  let base : ∀ i, Ω i := Classical.choice <| by
    have hbase := nonempty_of_finLaw (FinLaw.pi P)
    exact hbase
  let ext : ∀ i, Ω i := fun i => if hi : i ∈ S then z ⟨i, hi⟩ else base i
  have hevent (ω : ∀ i, Ω i) :
      (∀ (i : ι) (hi : i ∈ S), ω i = z ⟨i, hi⟩) ↔
        ∀ (i : ι) (hi : i ∈ S), ω i = ext i := by
    constructor
    · intro h i hi
      simpa [ext, hi] using h i hi
    · intro h i hi
      simpa [ext, hi] using h i hi
  calc
    (FinLaw.pi P).pr (fun ω => ∀ (i : ι) (hi : i ∈ S), ω i = z ⟨i, hi⟩) =
        (FinLaw.pi P).pr (fun ω => ∀ (i : ι) (hi : i ∈ S), ω i = ext i) := by
          congr 1
          funext ω
          exact propext (hevent ω)
    _ = ∏ i ∈ S, (P i).w (ext i) := pi_pr_cylinder P S ext
    _ = ∏ i : {i // i ∈ S}, (P i.1).w (z i) := by
          have h := Finset.prod_subtype (F := scopeFintype) (s := S) (h := fun _ => Iff.rfl)
            (fun i => (P i).w (ext i))
          simpa [ext] using h

/-- The mass of a pushforward atom is its preimage probability. -/
theorem map_weight_eq_pr {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (P : FinLaw Ω) (f : Ω → Ξ) (z : Ξ) :
    (FinLaw.map P f).w z = P.pr (fun ω => f ω = z) := by
  classical
  unfold FinLaw.map FinLaw.pr
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : f ω = z <;> simp [h]

/-- Every nonzero pushforward atom has a nonzero preimage atom. -/
theorem map_support_exists {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (P : FinLaw Ω) (f : Ω → Ξ) (z : Ξ) (h : (FinLaw.map P f).w z ≠ 0) :
    ∃ x, f x = z ∧ P.w x ≠ 0 := by
  classical
  unfold FinLaw.map at h
  by_contra hn
  have hzero : ∀ x, (if f x = z then P.w x else 0) = 0 := by
    intro x
    by_cases hfx : f x = z
    · have hw : P.w x = 0 := by
        by_contra hw
        exact hn ⟨x, hfx, hw⟩
      simp [hfx, hw]
    · simp [hfx]
  exact h (by simp [hzero])

/-- Marginalizing a product law to a coordinate subtype gives the product of its marginal laws. -/
theorem finLaw_ext {Ω : Type*} [Fintype Ω] {P Q : FinLaw Ω}
    (h : ∀ x, P.w x = Q.w x) : P = Q := by
  cases P with
  | mk w₁ h₁ h₂ =>
    cases Q with
    | mk w₂ k₁ k₂ =>
      have hw : w₁ = w₂ := funext h
      subst w₂
      cases Subsingleton.elim h₁ k₁
      cases Subsingleton.elim h₂ k₂
      rfl

/-- Marginalizing a product law to a coordinate subtype gives the product of its marginal laws. -/
theorem pi_map_subtype {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (S : Finset ι) :
    FinLaw.map (FinLaw.pi P) (fun (ω : ∀ i, Ω i) (i : {i // i ∈ S}) => ω i.1) =
      FinLaw.pi (fun i : {i // i ∈ S} => P i.1) := by
  classical
  apply finLaw_ext
  intro z
  rw [map_weight_eq_pr]
  have hevent (ω : ∀ i, Ω i) :
      ((fun (i : {i // i ∈ S}) => ω i.1) = z) ↔
        ∀ (i : ι) (hi : i ∈ S), ω i = z ⟨i, hi⟩ := by
    constructor
    · intro h i hi
      exact congrFun h ⟨i, hi⟩
    · intro h
      funext i
      exact h i.1 i.2
  rw [show (fun ω : ∀ i, Ω i => (fun i : {i // i ∈ S} => ω i.1) = z) =
      (fun ω => ∀ (i : ι) (hi : i ∈ S), ω i = z ⟨i, hi⟩) from
        funext fun ω => propext (hevent ω)]
  rw [pi_pr_subtype_cylinder]
  simp [FinLaw.pi]

/-- Expectations of a test on selected coordinates reduce to their product marginal. -/
theorem pi_subtype_expect {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (S : Finset ι)
    (f : (∀ i : {i // i ∈ S}, Ω i.1) → ℝ) :
    (FinLaw.pi P).E (fun ω => f (fun i => ω i.1)) =
      (FinLaw.pi (fun i : {i // i ∈ S} => P i.1)).E f := by
  rw [← map_expect (FinLaw.pi P) (fun ω (i : {i // i ∈ S}) => ω i.1) f]
  rw [pi_map_subtype]

/-- Atom weights of a product marginal are the corresponding coordinate product. -/
theorem pi_subtype_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (S : Finset ι)
    (z : ∀ i : {i // i ∈ S}, Ω i.1) :
    (FinLaw.pi (fun i : {i // i ∈ S} => P i.1)).w z =
      ∏ i : {i // i ∈ S}, (P i.1).w (z i) := rfl

end HypercubeRamsey.S16.Lane_q_s16_comp2
