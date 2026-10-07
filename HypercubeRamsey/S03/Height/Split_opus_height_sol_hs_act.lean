import HypercubeRamsey.S03.Height.Selection_p_height_main

set_option maxHeartbeats 400000

namespace HypercubeRamsey.Lane_sol_hs_act

open OAI.HypercubeRamsey Lane_p_height_main
open scoped BigOperators

/-- Changing bad statuses only needs to preserve the statuses inside the stopped ball. -/
theorem failure_mono {p : HDParams} (Sites : p.Sites)
    (bad bad' : CubeVertex p.d → ℕ → Prop) (x : HDState p) (R : ℕ) (η : ℝ)
    (h : ∀ v j, hdScaleDistance p.D x (v, j) < R → bad v j → bad' v j) :
    hdScaleThresholdFailure Sites bad x R η → hdScaleThresholdFailure Sites bad' x R η := by
  have convert : ∀ {start finish : HDState p},
      HDThresholdWalk Sites bad x R start finish → HDThresholdWalk Sites bad' x R start finish := by
    intro start finish walk
    induction walk with
    | stop hb => exact HDThresholdWalk.stop hb
    | up hi hv hj hb tail ih => exact HDThresholdWalk.up hi hv hj (h _ _ hi hb) ih
    | down hi hv hj hs tail ih => exact HDThresholdWalk.down hi hv hj hs ih
  rintro ⟨finish, ⟨walk⟩, hrise⟩
  exact ⟨finish, ⟨convert walk⟩, hrise⟩

/-- A coordinate swap proves independence without an appeal to Finner. -/
theorem expect_mul_disjoint {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (Q : ι → FinProb Ω) (S T : Finset ι) (hST : Disjoint S T)
    (f g : (ι → Ω) → ℝ) (hf : FinProb.DependsOn f S) (hg : FinProb.DependsOn g T) :
    (FinProb.pi Q).expect (fun ω => f ω * g ω) =
      (FinProb.pi Q).expect f * (FinProb.pi Q).expect g := by
  classical
  let mix : (ι → Ω) → (ι → Ω) → (ι → Ω) := fun a b i => if i ∈ S then a i else b i
  let e : ((ι → Ω) × (ι → Ω)) ≃ ((ι → Ω) × (ι → Ω)) :=
    { toFun := fun ab => (mix ab.1 ab.2, mix ab.2 ab.1)
      invFun := fun ab => (mix ab.1 ab.2, mix ab.2 ab.1)
      left_inv := by intro ab; ext i <;> by_cases hi : i ∈ S <;> simp [mix, hi]
      right_inv := by intro ab; ext i <;> by_cases hi : i ∈ S <;> simp [mix, hi] }
  let W : (ι → Ω) → ℝ := (FinProb.pi Q).w
  have hw (a b : ι → Ω) : W (mix a b) * W (mix b a) = W a * W b := by
    change (∏ i, (Q i).w (mix a b i)) * (∏ i, (Q i).w (mix b a i)) =
      (∏ i, (Q i).w (a i)) * (∏ i, (Q i).w (b i))
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [mix, hi, mul_comm]
  have hfm (a b : ι → Ω) : f (mix a b) = f a :=
    hf _ _ (fun i hi => by simp [mix, hi])
  have hgm (a b : ι → Ω) : g (mix a b) = g b := by
    apply hg
    intro i hi
    have hn : i ∉ S := fun hs => (Finset.disjoint_left.mp hST) hs hi
    simp [mix, hn]
  have hsum : (∑ b, W b) = 1 := (FinProb.pi Q).sum_eq_one
  calc
    (FinProb.pi Q).expect (fun ω => f ω * g ω)
        = ∑ ab : (ι → Ω) × (ι → Ω), W ab.1 * W ab.2 * (f ab.1 * g ab.1) := by
          rw [Fintype.sum_prod_type]
          unfold FinProb.expect
          apply Finset.sum_congr rfl
          intro a _
          calc
            W a * (f a * g a) = W a * (f a * g a) * ∑ b, W b := by rw [hsum, mul_one]
            _ = ∑ b, W a * W b * (f a * g a) := by rw [Finset.mul_sum]; congr 1; funext b; ring
    _ = ∑ ab : (ι → Ω) × (ι → Ω), W (e ab).1 * W (e ab).2 *
          (f (e ab).1 * g (e ab).1) := by
          exact (Equiv.sum_comp e (fun ab => W ab.1 * W ab.2 * (f ab.1 * g ab.1))).symm
    _ = ∑ ab : (ι → Ω) × (ι → Ω), W ab.1 * W ab.2 * (f ab.1 * g ab.2) := by
          apply Finset.sum_congr rfl
          intro ab _
          change W (mix ab.1 ab.2) * W (mix ab.2 ab.1) *
            (f (mix ab.1 ab.2) * g (mix ab.1 ab.2)) = _
          rw [hw, hfm, hgm]
    _ = (FinProb.pi Q).expect f * (FinProb.pi Q).expect g := by
          rw [Fintype.sum_prod_type]
          unfold FinProb.expect
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          dsimp [W]
          ring

/-- Products of functions on pairwise disjoint coordinate sets factor exactly. -/
theorem expect_prod_disjoint {ι Ω B : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq B] (Q : ι → FinProb Ω)
    (Y : Finset B) (S : B → Finset ι) (f : B → (ι → Ω) → ℝ)
    (hdisj : ∀ b ∈ Y, ∀ c ∈ Y, b ≠ c → Disjoint (S b) (S c))
    (hscope : ∀ b ∈ Y, FinProb.DependsOn (f b) (S b)) :
    (FinProb.pi Q).expect (fun ω => ∏ b ∈ Y, f b ω) =
      ∏ b ∈ Y, (FinProb.pi Q).expect (f b) := by
  classical
  induction Y using Finset.induction_on with
  | empty => simp [FinProb.expect, (FinProb.pi Q).sum_eq_one]
  | @insert b Y hb ih =>
      have hd : Disjoint (S b) (Y.biUnion S) := by
        apply Finset.disjoint_left.mpr
        intro i hi hj
        obtain ⟨c, hc, hic⟩ := Finset.mem_biUnion.mp hj
        exact Finset.disjoint_left.mp (hdisj b (by simp) c (by simp [hc])
          (fun h => hb (h ▸ hc))) hi hic
      have hrest : FinProb.DependsOn (fun ω => ∏ c ∈ Y, f c ω) (Y.biUnion S) := by
        intro a a' haa
        apply Finset.prod_congr rfl
        intro c hc
        apply hscope c (by simp [hc])
        intro i hi
        exact haa i (Finset.mem_biUnion.mpr ⟨c, hc, hi⟩)
      simp only [Finset.prod_insert hb]
      rw [expect_mul_disjoint Q _ _ hd _ _ (hscope b (by simp)) hrest]
      rw [ih (fun c hc d hd hne => hdisj c (by simp [hc]) d (by simp [hd]) hne)
        (fun c hc => hscope c (by simp [hc]))]

/-- Pairwise overlap bounds control the number of centers discarded from a private region. -/
theorem private_loss {ι B : Type*} [DecidableEq ι] [DecidableEq B]
    (C F : Finset ι) (D : B → Finset ι) (Y : Finset B) (y : B) (hy : y ∈ Y)
    (Q : ι → Prop) [DecidablePred Q] (δ : ℝ) (hδ : 0 ≤ δ)
    (hF : ∀ i ∈ F, i ∈ C ∧ i ∈ D y ∧ Q i)
    (hov : ∀ z ∈ Y, y ≠ z → (((C ∩ D y ∩ D z).filter Q).card : ℝ) ≤ δ / Y.card) :
    (F.card : ℝ) ≤
      ((F.filter (fun i => ∀ z ∈ Y, z ≠ y → i ∉ D z)).card : ℝ) + δ := by
  classical
  let G := F.filter (fun i => ∀ z ∈ Y, z ≠ y → i ∉ D z)
  let O := fun z => if z = y then ∅ else (C ∩ D y ∩ D z).filter Q
  have hsub : F \ G ⊆ Y.biUnion O := by
    intro i hi
    obtain ⟨hiF, hiG⟩ := Finset.mem_sdiff.mp hi
    have hn : ¬ (∀ z ∈ Y, z ≠ y → i ∉ D z) := by
      intro h
      exact hiG (Finset.mem_filter.mpr ⟨hiF, h⟩)
    push_neg at hn
    obtain ⟨z, hz, hzy, hiz⟩ := hn
    obtain ⟨hiC, hiy, hiQ⟩ := hF i hiF
    apply Finset.mem_biUnion.mpr
    refine ⟨z, hz, ?_⟩
    simp only [O, if_neg hzy, Finset.mem_filter, Finset.mem_inter]
    exact ⟨⟨⟨hiC, hiy⟩, hiz⟩, hiQ⟩
  have hsum : ((F \ G).card : ℝ) ≤ δ := by
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
    have hcard' : ((F \ G).card : ℝ) ≤ ∑ z ∈ Y, ((O z).card : ℝ) := by
      exact_mod_cast hcard
    have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast Finset.card_pos.mpr ⟨y, hy⟩
    calc
      ((F \ G).card : ℝ) ≤ ∑ z ∈ Y, ((O z).card : ℝ) := hcard'
      _ ≤ ∑ z ∈ Y, δ / Y.card := by
        apply Finset.sum_le_sum
        intro z hz
        by_cases hzy : z = y
        · simp [O, hzy, div_nonneg hδ hYpos.le]
        · simpa [O, hzy] using hov z hz (Ne.symm hzy)
      _ = δ := by simp [mul_div_cancel₀ _ hYpos.ne']
  have heq := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ F : G ⊆ F)
  have heq' : ((F \ G).card : ℝ) + (G.card : ℝ) = F.card := by exact_mod_cast heq
  change (F.card : ℝ) ≤ (G.card : ℝ) + δ
  linarith

/-- The probability of scoped events on disjoint coordinates is the product of probabilities. -/
theorem pr_all_disjoint {ι Ω B : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq B] (Q : ι → FinProb Ω)
    (Y : Finset B) (S : B → Finset ι) (F : B → (ι → Ω) → Prop)
    (hdisj : ∀ b ∈ Y, ∀ c ∈ Y, b ≠ c → Disjoint (S b) (S c))
    (hscope : ∀ b ∈ Y, FinProb.DependsOn (F b) (S b)) :
    (FinProb.pi Q).pr (fun ω => ∀ b ∈ Y, F b ω) =
      ∏ b ∈ Y, (FinProb.pi Q).pr (F b) := by
  classical
  let f : B → (ι → Ω) → ℝ := fun b ω => if F b ω then 1 else 0
  have hind (ω : ι → Ω) : (∏ b ∈ Y, f b ω) = if ∀ b ∈ Y, F b ω then 1 else 0 := by
    by_cases h : ∀ b ∈ Y, F b ω
    · rw [if_pos h]
      exact Finset.prod_eq_one (fun b hb => by simp [f, h b hb])
    · rw [if_neg h]
      push_neg at h
      obtain ⟨b, hb, hFb⟩ := h
      exact Finset.prod_eq_zero hb (by simp [f, hFb])
  have he (b : B) : (FinProb.pi Q).expect (f b) = (FinProb.pi Q).pr (F b) := by
    unfold FinProb.expect FinProb.pr
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : F b ω <;> simp [f, h]
  have hf : ∀ b ∈ Y, FinProb.DependsOn (f b) (S b) := by
    intro b hb ω ω' haa
    dsimp [f]
    rw [hscope b hb ω ω' haa]
  have hfact := expect_prod_disjoint Q Y S f hdisj hf
  simp only [he] at hfact
  rw [← hfact]
  unfold FinProb.pr FinProb.expect
  apply Finset.sum_congr rfl
  intro ω _
  conv_rhs =>
    arg 2
    change ∏ b ∈ Y, f b ω
    rw [hind]
  split_ifs <;> simp

end HypercubeRamsey.Lane_sol_hs_act
