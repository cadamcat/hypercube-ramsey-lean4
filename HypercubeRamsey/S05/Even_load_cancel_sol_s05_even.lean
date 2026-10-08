import HypercubeRamsey.S05.Even_test_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

variable {Ω Z D : Type*} [Fintype Ω] [Fintype Z] [Fintype D]

def resampledMass (π : FinProb Z) (replace : Ω → Z → Ω) (F : Ω → D → ℝ)
    (ω : Ω) (d : D) : ℝ := ∑ z, π.w z * F (replace ω z) d

def posteriorAverage (π : FinProb Z) (replace : Ω → Z → Ω) (F : Ω → D → ℝ)
    (g : Ω → ℝ) (ω : Ω) (d : D) : ℝ :=
  (∑ z, π.w z * F (replace ω z) d * g (replace ω z)) / resampledMass π replace F ω d

theorem mass_mul_posteriorAverage (π : FinProb Z) (replace : Ω → Z → Ω) (F : Ω → D → ℝ)
    (g : Ω → ℝ) (hF : ∀ ω d, 0 ≤ F ω d) (ω : Ω) (d : D) :
    resampledMass π replace F ω d * posteriorAverage π replace F g ω d =
      ∑ z, π.w z * F (replace ω z) d * g (replace ω z) := by
  by_cases hm : resampledMass π replace F ω d = 0
  · have hz (z : Z) : π.w z * F (replace ω z) d = 0 := by
      have hle := Finset.single_le_sum (fun z _ => mul_nonneg (π.nonneg z) (hF (replace ω z) d)) (Finset.mem_univ z)
      change π.w z * F (replace ω z) d ≤ resampledMass π replace F ω d at hle
      rw [hm] at hle
      exact le_antisymm hle (mul_nonneg (π.nonneg z) (hF _ d))
    rw [hm, zero_mul]
    simp_rw [hz, zero_mul]
    simp
  · exact mul_div_cancel₀ _ hm

theorem posteriorAverage_replace (π : FinProb Z) (replace : Ω → Z → Ω) (F : Ω → D → ℝ)
    (g : Ω → ℝ) (hreplace : ∀ ω z z', replace (replace ω z) z' = replace ω z')
    (ω : Ω) (z : Z) (d : D) :
    posteriorAverage π replace F g (replace ω z) d = posteriorAverage π replace F g ω d := by
  unfold posteriorAverage resampledMass
  simp_rw [hreplace]

theorem posterior_average_cancellation (P : FinProb Ω) (π : FinProb Z)
    (replace : Ω → Z → Ω) (F : Ω → D → ℝ) (g : Ω → ℝ)
    (hF : ∀ ω d, 0 ≤ F ω d)
    (hreplace : ∀ ω z z', replace (replace ω z) z' = replace ω z')
    (hresample : ∀ f : Ω → ℝ, P.expect (fun ω => π.expect (fun z => f (replace ω z))) = P.expect f) :
    P.expect (fun ω => ∑ d, F ω d * posteriorAverage π replace F g ω d) =
      P.expect (fun ω => g ω * ∑ d, F ω d) := by
  calc
    _ = P.expect (fun ω => π.expect (fun z => ∑ d,
        F (replace ω z) d * posteriorAverage π replace F g (replace ω z) d)) := (hresample (fun ω => ∑ d, F ω d * posteriorAverage π replace F g ω d)).symm
    _ = P.expect (fun ω => ∑ d, resampledMass π replace F ω d * posteriorAverage π replace F g ω d) := by
      congr 1
      funext ω
      unfold FinProb.expect
      simp_rw [posteriorAverage_replace π replace F g hreplace]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      unfold resampledMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = P.expect (fun ω => ∑ d, ∑ z, π.w z * F (replace ω z) d * g (replace ω z)) := by
      simp_rw [mass_mul_posteriorAverage π replace F g hF]
    _ = P.expect (fun ω => π.expect (fun z => ∑ d, F (replace ω z) d * g (replace ω z))) := by
      congr 1
      funext ω
      unfold FinProb.expect
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ = P.expect (fun ω => ∑ d, F ω d * g ω) := hresample (fun ω => ∑ d, F ω d * g ω)
    _ = _ := by
      congr 1
      funext ω
      rw [← Finset.sum_mul, mul_comm]

theorem posterior_average_selection_bound (P : FinProb Ω) (π : FinProb Z)
    (replace : Ω → Z → Ω) (F : Ω → D → ℝ) (g : Ω → ℝ) (select : Ω → Prop)
    (hF : ∀ ω d, 0 ≤ F ω d) (hg : ∀ ω, 0 ≤ g ω)
    (hreplace : ∀ ω z z', replace (replace ω z) z' = replace ω z')
    (hresample : ∀ f : Ω → ℝ, P.expect (fun ω => π.expect (fun z => f (replace ω z))) = P.expect f)
    (hsel : ∀ ω, ∑ d, F ω d ≤ if select ω then (1 : ℝ) else 0) :
    P.expect (fun ω => ∑ d, F ω d * posteriorAverage π replace F g ω d) ≤
      P.expect (fun ω => if select ω then g ω else 0) := by
  rw [posterior_average_cancellation P π replace F g hF hreplace hresample]
  unfold FinProb.expect
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (P.nonneg ω)
  have h := mul_le_mul_of_nonneg_left (hsel ω) (hg ω)
  simpa only [mul_ite, mul_one, mul_zero] using h

end
end HypercubeRamsey.Lane_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even
open scoped BigOperators

/-- A selected subtuple has no more hits than the full pool. This avoids enumerating high subsets. -/
theorem subtuple_empirical_le_pool {I J V : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (S : Finset I) (z : I → J → V) (x : V) [DecidableEq V]
    (hs : 0 < S.card) (hJ : 0 < Fintype.card J) :
    ((Finset.univ.filter fun e : S × J => z e.1.1 e.2 = x).card : ℝ) /
        ((S.card * Fintype.card J : ℕ) : ℝ) ≤
      (Fintype.card I : ℝ) / S.card *
        (((Finset.univ.filter fun e : I × J => z e.1 e.2 = x).card : ℝ) /
          ((Fintype.card I * Fintype.card J : ℕ) : ℝ)) := by
  classical
  have hI : 0 < Fintype.card I :=
    lt_of_lt_of_le hs (Finset.card_le_univ S)
  have hsR : (0 : ℝ) < S.card := by exact_mod_cast hs
  have hJR : (0 : ℝ) < Fintype.card J := by exact_mod_cast hJ
  have hIR : (0 : ℝ) < Fintype.card I := by exact_mod_cast hI
  let f : S × J → I × J := fun e => (e.1.1, e.2)
  have hf : Function.Injective f := by
    intro a b hab
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hab
    · exact congrArg (fun e : I × J => e.2) hab
  have hsub : (Finset.univ.filter (fun e : S × J => z e.1.1 e.2 = x)).image f ⊆
      Finset.univ.filter (fun e : I × J => z e.1 e.2 = x) := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he').2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf] at hcard
  have hcardR : ((Finset.univ.filter fun e : S × J => z e.1.1 e.2 = x).card : ℝ) ≤
      ((Finset.univ.filter fun e : I × J => z e.1 e.2 = x).card : ℝ) := by exact_mod_cast hcard
  push_cast
  have heq : (Fintype.card I : ℝ) / S.card *
      (((Finset.univ.filter fun e : I × J => z e.1 e.2 = x).card : ℝ) /
        ((Fintype.card I : ℝ) * Fintype.card J)) =
      ((Finset.univ.filter fun e : I × J => z e.1 e.2 = x).card : ℝ) /
        ((S.card : ℝ) * Fintype.card J) := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right hcardR (mul_nonneg hsR.le hJR.le)

end HypercubeRamsey.Lane_sol_s05_even
