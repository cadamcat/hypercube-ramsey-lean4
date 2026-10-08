import HypercubeRamsey.S03.Height.Device

/-! Supporting lemmas for lane sol-s10-d56. -/

namespace HypercubeRamsey.Lane_sol_s10_d56

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- Erasing eligibility at one site leaves eligibility at every other site unchanged. -/
noncomputable def eraseSite (p : HDParams) (E : p.EligMap)
    (u : CubeVertex p.d) : p.EligMap :=
  fun v j => if v = u then ∅ else E v j

theorem eraseSite_legalAt (p : HDParams) (P : p.Loc → Bool) (E : p.EligMap)
    (u v : CubeVertex p.d) (hne : v ≠ u) (j : Fin (p.H + 1)) :
    p.LegalAt P (eraseSite p E u) v j ↔ p.LegalAt P E v j := by
  simp only [HDParams.LegalAt, eraseSite, if_neg hne]

theorem eraseSite_legal_on (p : HDParams) (P : p.Loc → Bool) (E : p.EligMap)
    (u : CubeVertex p.d) (dom : p.Sites) (hu : u ∉ dom)
    (hlegal : p.Legal P E dom) :
    p.Legal P (eraseSite p E u) dom := by
  intro v hv j
  have hne : v ≠ u := by
    intro h
    exact hu (h ▸ hv)
  exact (eraseSite_legalAt p P E u v hne j).mpr (hlegal v hv j)

theorem eraseSite_not_legal (p : HDParams) (hlam : 0 < p.lam)
    (P : p.Loc → Bool) (E : p.EligMap) (u : CubeVertex p.d)
    (dom : p.Sites) (hu : u ∈ dom) :
    ¬ p.Legal P (eraseSite p E u) dom := by
  intro h
  have hsize := (h u hu ⟨0, by omega⟩).2
  simp [eraseSite] at hsize
  linarith

theorem eraseSite_bad (p : HDParams) (P A : p.Loc → Bool) (E : p.EligMap)
    (u : CubeVertex p.d) (j : Fin (p.H + 1)) :
    p.Bad P A (eraseSite p E u) u j := by
  apply Or.inl
  simp [eraseSite]

/-- An unchecked empty site can climb through every height level. -/
theorem eraseSite_reach (p : HDParams) (P A : p.Loc → Bool) (E : p.EligMap)
    (Sites : p.Sites) (u v : CubeVertex p.d) (R : ℕ)
    (hu : u ∈ Sites) (huR : hammingDist u v ≤ R) :
    ∀ j ≤ p.H, p.Reach Sites P A (eraseSite p E u) v R u j := by
  intro j hj
  induction j with
  | zero => exact HDParams.Reach.start u hu huR
  | succ j ih =>
      apply HDParams.Reach.up u j (by omega) (ih (by omega))
      exact ⟨by omega, eraseSite_bad p P A E u ⟨j, by omega⟩⟩

/-- The unchecked site propagates its height to a nearby checked query. -/
theorem eraseSite_height_lower (p : HDParams) (hH : 1 ≤ p.H)
    (P A : p.Loc → Bool) (E : p.EligMap) (Sites : p.Sites)
    (u v : CubeVertex p.d) (R : ℕ) (hu : u ∈ Sites) (hv : v ∈ Sites)
    (huR : hammingDist u v ≤ R) (hstep : hammingDist u v ≤ p.D) :
    p.H - 1 ≤ p.height Sites P A (eraseSite p E u) R v := by
  have hreach := eraseSite_reach p P A E Sites u v R hu huR p.H le_rfl
  have hreach' : p.Reach Sites P A (eraseSite p E u) v R u (p.H - 1 + 1) := by
    simpa only [Nat.sub_add_cancel hH] using hreach
  have hv0 : hammingDist v v ≤ R := by simp
  have hdown := HDParams.Reach.down u v (p.H - 1) hreach' hv hv0 hstep
  unfold HDParams.height
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), hdown⟩)

/-- With local size gates alone, the positive-height event may have probability one.
This is an obstruction to applying the consultation-domain height estimate. -/
theorem local_legal_positive_height_pr_one (p : HDParams) (hH : 2 ≤ p.H)
    (P : p.Loc → Bool) (E : p.EligMap) (Sites : p.Sites)
    (u v : CubeVertex p.d) (hu : u ∈ Sites) (hv : v ∈ Sites)
    (hne : v ≠ u) (huR : hammingDist u v ≤ p.Rlong)
    (hstep : hammingDist u v ≤ p.D)
    (hlegal : ∀ j, p.LegalAt P E v j) :
    (∀ j, p.LegalAt P (eraseSite p E u) v j) ∧
      p.actLaw.pr (fun A =>
        0 < p.height Sites P A (eraseSite p E u) p.Rlong v) = 1 := by
  constructor
  · intro j
    exact (eraseSite_legalAt p P E u v hne j).mpr (hlegal j)
  · have hpos : ∀ A, 0 < p.height Sites P A (eraseSite p E u) p.Rlong v := by
      intro A
      have hh := eraseSite_height_lower p (by omega) P A E Sites u v p.Rlong
        hu hv huR hstep
      omega
    simp only [FinProb.pr, if_pos (hpos _)]
    exact p.actLaw.sum_eq_one

/-- Five coordinates in the nonzero coset cannot have syndrome in the kernel. -/
theorem five_coset_sum_not_subset {G : Type*} [AddCommGroup G] [DecidableEq G]
    (f : G →+ ZMod 2) (σ : G) (C U : Finset G)
    (hσ : f σ = 0) (hC : ∀ x ∈ C, f x = 1)
    (hU : U.card = 5) (hsum : ∑ x ∈ U, x = σ) : ¬ U ⊆ C := by
  intro hsub
  have hones : (∑ x ∈ U, f x) = (1 : ZMod 2) := by
    calc
      (∑ x ∈ U, f x) = ∑ _x ∈ U, (1 : ZMod 2) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hC x (hsub hx)
      _ = (5 : ZMod 2) := by simp [hU]
      _ = 1 := by decide
  have hzero : (∑ x ∈ U, f x) = 0 := by
    rw [← map_sum, hsum, hσ]
  have hbad : (1 : ZMod 2) = 0 := hones.symm.trans hzero
  norm_num at hbad

/-- A support of size `r+5` in the nonzero coset is farther than `r` from
any gated odd support of size at most five with kernel syndrome. The two
set differences count the differing bits after cancelling the base word. -/
theorem ghost_support_distance {G : Type*} [AddCommGroup G] [DecidableEq G]
    (f : G →+ ZMod 2) (σ : G) (C U : Finset G) (r : ℕ)
    (hσ : f σ = 0) (hC : ∀ x ∈ C, f x = 1)
    (hCcard : C.card = r + 5) (hUodd : Odd U.card) (hUbound : U.card ≤ 5)
    (hsum : ∑ x ∈ U, x = σ) :
    r + 2 ≤ (C \ U).card + (U \ C).card := by
  have hcard₁ := Finset.card_sdiff_add_card_inter C U
  have hcard₂ := Finset.card_sdiff_add_card_inter U C
  rw [Finset.inter_comm U C] at hcard₂
  have hinter_le : (C ∩ U).card ≤ U.card :=
    Finset.card_le_card Finset.inter_subset_right
  by_cases hsmall : U.card ≤ 3
  · omega
  · have hfive : U.card = 5 := by
      rcases hUodd with ⟨k, hk⟩
      omega
    have hnot : ¬ U ⊆ C := five_coset_sum_not_subset f σ C U hσ hC hfive hsum
    have hne : C ∩ U ≠ U := by
      intro heq
      apply hnot
      intro x hx
      exact (Finset.mem_inter.mp (heq.symm ▸ hx)).1
    have hlt : (C ∩ U).card < U.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.inter_subset_right, hne⟩)
    omega

/-- The same ghost support is at distance exactly `r` from an ungated
five-bit envelope word whose support is contained in it. -/
theorem ghost_envelope_distance {α : Type*} [DecidableEq α]
    (C S : Finset α) (r : ℕ) (hsub : S ⊆ C)
    (hC : C.card = r + 5) (hS : S.card = 5) :
    (C \ S).card + (S \ C).card = r := by
  rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.card_empty, add_zero,
    Finset.card_sdiff_of_subset hsub, hC, hS]
  omega

/-! Sharp level-zero selection estimate, using the height device's swap symmetry. -/

private lemma finProb_pr_mono {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
    (A B : Ω → Prop) (hAB : ∀ ω, A ω → B ω) : μ.pr A ≤ μ.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω <;> simp [hA, hB, μ.nonneg]

private def tieMinEvent (p : HDParams) (S : Finset p.Loc) (x : p.Loc)
    (A : p.Loc → Bool) (τ : p.Ties) (ℓ : p.Loc) : Prop :=
  A ℓ = true ∧ ∀ m ∈ S, A m = true → p.priority τ x ℓ ≤ p.priority τ x m

private def actSwapEquiv (p : HDParams) (a b : p.Loc) :
    (p.Loc → Bool) ≃ (p.Loc → Bool) where
  toFun A := fun ℓ => A (Equiv.swap a b ℓ)
  invFun A := fun ℓ => A (Equiv.swap a b ℓ)
  left_inv := by intro A; funext ℓ; simp
  right_inv := by intro A; funext ℓ; simp

private noncomputable def locIndexSwap (p : HDParams) (a b : p.Loc) :
    Equiv.Perm (Fin (Fintype.card p.Loc)) :=
  (Fintype.equivFin p.Loc).symm.trans ((Equiv.swap a b).trans (Fintype.equivFin p.Loc))

private theorem locIndexSwap_apply (p : HDParams) (a b ℓ : p.Loc) :
    locIndexSwap p a b (Fintype.equivFin p.Loc ℓ) =
      Fintype.equivFin p.Loc (Equiv.swap a b ℓ) := by
  simp [locIndexSwap, Equiv.trans_apply]

private noncomputable def tieSwap (p : HDParams) (x a b : p.Loc) (τ : p.Ties) : p.Ties :=
  Function.update τ x ((locIndexSwap p a b).trans (τ x))

private theorem tieSwap_involutive (p : HDParams) (x a b : p.Loc) (τ : p.Ties) :
    tieSwap p x a b (tieSwap p x a b τ) = τ := by
  funext y
  by_cases hy : y = x
  · subst y
    apply Equiv.ext
    intro k
    simp [tieSwap, locIndexSwap, Equiv.trans_apply]
  · simp [tieSwap, hy]

private noncomputable def tieSwapEquiv (p : HDParams) (x a b : p.Loc) : p.Ties ≃ p.Ties where
  toFun := tieSwap p x a b
  invFun := tieSwap p x a b
  left_inv := tieSwap_involutive p x a b
  right_inv := tieSwap_involutive p x a b

private noncomputable def sampleSwapEquiv (p : HDParams) (x a b : p.Loc) :
    ((p.Loc → Bool) × p.Ties) ≃ ((p.Loc → Bool) × p.Ties) :=
  Equiv.prodCongr (actSwapEquiv p a b) (tieSwapEquiv p x a b)

private theorem tieSwap_priority (p : HDParams) (x a b ℓ : p.Loc) (τ : p.Ties) :
    p.priority (tieSwap p x a b τ) x ℓ = p.priority τ x (Equiv.swap a b ℓ) := by
  simp [HDParams.priority, tieSwap, locIndexSwap_apply]

private theorem actSwap_weight (p : HDParams) (a b : p.Loc) (A : p.Loc → Bool) :
    p.actLaw.w (actSwapEquiv p a b A) = p.actLaw.w A := by
  change (∏ ℓ : p.Loc,
      (FinProb.bernoulli ((p.n : ℝ) ^ p.b₀ / p.lam)).w
        (A (Equiv.swap a b ℓ))) =
    ∏ ℓ : p.Loc, (FinProb.bernoulli ((p.n : ℝ) ^ p.b₀ / p.lam)).w (A ℓ)
  exact Fintype.prod_equiv (Equiv.swap a b)
    (fun ℓ => (FinProb.bernoulli ((p.n : ℝ) ^ p.b₀ / p.lam)).w
      (A (Equiv.swap a b ℓ)))
    (fun ℓ => (FinProb.bernoulli ((p.n : ℝ) ^ p.b₀ / p.lam)).w (A ℓ))
    (fun _ => rfl)

private theorem tieSwap_weight (p : HDParams) (x a b : p.Loc) (τ : p.Ties) :
    p.tieLaw.w (tieSwap p x a b τ) = p.tieLaw.w τ := by
  simp [HDParams.tieLaw, FinProb.pi, FinProb.uniformAll]

private theorem sampleSwap_weight (p : HDParams) (x a b : p.Loc)
    (ω : (p.Loc → Bool) × p.Ties) :
    (p.actLaw.prod p.tieLaw).w (sampleSwapEquiv p x a b ω) =
      (p.actLaw.prod p.tieLaw).w ω := by
  rcases ω with ⟨A, τ⟩
  change p.actLaw.w (actSwapEquiv p a b A) * p.tieLaw.w (tieSwap p x a b τ) =
    p.actLaw.w A * p.tieLaw.w τ
  rw [actSwap_weight, tieSwap_weight]

private theorem swap_mem_iff (p : HDParams) (S : Finset p.Loc) (a b : p.Loc)
    (ha : a ∈ S) (hb : b ∈ S) (m : p.Loc) :
    m ∈ S ↔ Equiv.swap a b m ∈ S := by
  by_cases hma : m = a
  · subst m
    simp [ha, hb]
  · by_cases hmb : m = b
    · subst m
      simp [ha, hb]
    · rw [Equiv.swap_apply_of_ne_of_ne hma hmb]

private theorem tieMinEvent_swap (p : HDParams) (S : Finset p.Loc) (x a b : p.Loc)
    (ha : a ∈ S) (hb : b ∈ S) (ω : (p.Loc → Bool) × p.Ties) :
    tieMinEvent p S x (sampleSwapEquiv p x a b ω).1
        (sampleSwapEquiv p x a b ω).2 a ↔
      tieMinEvent p S x ω.1 ω.2 b := by
  rcases ω with ⟨A, τ⟩
  change tieMinEvent p S x (actSwapEquiv p a b A) (tieSwap p x a b τ) a ↔
    tieMinEvent p S x A τ b
  constructor
  · rintro ⟨hactive, hmin⟩
    refine ⟨?_, ?_⟩
    · simpa [actSwapEquiv] using hactive
    · intro m hm hAm
      have hm' : Equiv.swap a b m ∈ S := (swap_mem_iff p S a b ha hb m).mp hm
      have hAm' : (actSwapEquiv p a b A) (Equiv.swap a b m) = true := by
        simpa [actSwapEquiv, Equiv.swap_apply_self] using hAm
      have h := hmin (Equiv.swap a b m) hm' hAm'
      simpa [tieSwap_priority, Equiv.swap_apply_self] using h
  · rintro ⟨hactive, hmin⟩
    refine ⟨?_, ?_⟩
    · simpa [actSwapEquiv] using hactive
    · intro m hm hAm
      have hm' : Equiv.swap a b m ∈ S := (swap_mem_iff p S a b ha hb m).mp hm
      have hAm' : A (Equiv.swap a b m) = true := by
        simpa [actSwapEquiv, Equiv.swap_apply_self] using hAm
      have h := hmin (Equiv.swap a b m) hm' hAm'
      simpa [tieSwap_priority, Equiv.swap_apply_self] using h

private theorem finProb_pr_eq_of_equiv {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
    (e : Ω ≃ Ω) (A B : Ω → Prop)
    (hweight : ∀ ω, μ.w (e ω) = μ.w ω)
    (hevent : ∀ ω, A (e ω) ↔ B ω) : μ.pr A = μ.pr B := by
  classical
  calc
    μ.pr A = ∑ ω, if A (e ω) then μ.w (e ω) else 0 := by
      unfold FinProb.pr
      rw [← Equiv.sum_comp e]
    _ = μ.pr B := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hB : B ω
      · have hA : A (e ω) := (hevent ω).mpr hB
        simp [hA, hB, hweight]
      · have hA : ¬ A (e ω) := fun h => hB ((hevent ω).mp h)
        simp [hA, hB, hweight]

private theorem tieMinEvent_unique (p : HDParams) (S : Finset p.Loc) (x : p.Loc)
    (A : p.Loc → Bool) (τ : p.Ties) {a b : p.Loc}
    (ha : a ∈ S) (hb : b ∈ S)
    (hA : tieMinEvent p S x A τ a) (hB : tieMinEvent p S x A τ b) : a = b := by
  have hab : p.priority τ x a ≤ p.priority τ x b := hA.2 b hb hB.1
  have hba : p.priority τ x b ≤ p.priority τ x a := hB.2 a ha hA.1
  apply (Fintype.equivFin p.Loc).injective
  apply (τ x).injective
  simpa [HDParams.priority] using le_antisymm hab hba

open Classical in
private theorem tieMin_count_le_one (p : HDParams) (S : Finset p.Loc) (x : p.Loc)
    (A : p.Loc → Bool) (τ : p.Ties) :
    (∑ ℓ ∈ S, if tieMinEvent p S x A τ ℓ then (1 : ℝ) else 0) ≤ 1 := by
  classical
  rw [Finset.sum_boole]
  have hcard : (S.filter (fun ℓ => tieMinEvent p S x A τ ℓ)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact tieMinEvent_unique p S x A τ
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  exact_mod_cast hcard

private theorem tieMin_probability_sum_le_one (p : HDParams) (S : Finset p.Loc)
    (x : p.Loc) :
    (∑ ℓ ∈ S, (p.actLaw.prod p.tieLaw).pr
      (fun ω => tieMinEvent p S x ω.1 ω.2 ℓ)) ≤ 1 := by
  classical
  let μ := p.actLaw.prod p.tieLaw
  calc
    _ = ∑ ω, μ.w ω *
          (∑ ℓ ∈ S, if tieMinEvent p S x ω.1 ω.2 ℓ then (1 : ℝ) else 0) := by
      unfold FinProb.pr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      by_cases h : tieMinEvent p S x ω.1 ω.2 ℓ <;> simp [h, μ]
    _ ≤ ∑ ω, μ.w ω := by
      apply Finset.sum_le_sum
      intro ω hω
      have hcount := tieMin_count_le_one p S x ω.1 ω.2
      exact mul_le_of_le_one_right (μ.nonneg ω) hcount
    _ = 1 := μ.sum_eq_one

private theorem tieMin_probability_eq (p : HDParams) (S : Finset p.Loc) (x : p.Loc)
    (a b : p.Loc) (ha : a ∈ S) (hb : b ∈ S) :
    (p.actLaw.prod p.tieLaw).pr
        (fun ω => tieMinEvent p S x ω.1 ω.2 a) =
      (p.actLaw.prod p.tieLaw).pr
        (fun ω => tieMinEvent p S x ω.1 ω.2 b) := by
  let μ := p.actLaw.prod p.tieLaw
  exact finProb_pr_eq_of_equiv μ (sampleSwapEquiv p x a b)
    (fun ω => tieMinEvent p S x ω.1 ω.2 a)
    (fun ω => tieMinEvent p S x ω.1 ω.2 b)
    (sampleSwap_weight p x a b)
    (tieMinEvent_swap p S x a b ha hb)

private theorem tieMin_probability_le_inv (p : HDParams) (S : Finset p.Loc)
    (x ℓ₀ : p.Loc) (hℓ₀ : ℓ₀ ∈ S) :
    (p.actLaw.prod p.tieLaw).pr
      (fun ω => tieMinEvent p S x ω.1 ω.2 ℓ₀) ≤ (S.card : ℝ)⁻¹ := by
  have hsum := tieMin_probability_sum_le_one p S x
  have hsumEq :
      (∑ ℓ ∈ S, (p.actLaw.prod p.tieLaw).pr
        (fun ω => tieMinEvent p S x ω.1 ω.2 ℓ)) =
        (S.card : ℝ) * (p.actLaw.prod p.tieLaw).pr
          (fun ω => tieMinEvent p S x ω.1 ω.2 ℓ₀) := by
    calc
      _ = ∑ ℓ ∈ S, (p.actLaw.prod p.tieLaw).pr
          (fun ω => tieMinEvent p S x ω.1 ω.2 ℓ₀) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            exact tieMin_probability_eq p S x ℓ ℓ₀ hℓ hℓ₀
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hcard : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨ℓ₀, hℓ₀⟩)
  have hmul : (S.card : ℝ) * (p.actLaw.prod p.tieLaw).pr
      (fun ω => tieMinEvent p S x ω.1 ω.2 ℓ₀) ≤ 1 := by
    rw [← hsumEq]
    exact hsum
  rw [← one_div]
  rw [le_div_iff₀ hcard]
  nlinarith [hmul]

private theorem selected_zero_is_min (p : HDParams) (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties)
    (v : CubeVertex p.d) (ℓ₀ : p.Loc)
    (hheight : p.height Sites P A E p.Rlong v = 0)
    (hselect : p.selection Sites P A E τ v = some ℓ₀) :
    tieMinEvent p (E v ⟨0, by omega⟩) (v, ⟨0, by omega⟩) A τ ℓ₀ := by
  classical
  by_cases hH : 0 < p.H
  · simp [HDParams.selection, HDParams.selectionAt, hheight, hH] at hselect
    rcases hselect with ⟨_, ⟨hne, hchosen⟩⟩
    let j0 : Fin (p.H + 1) := ⟨0, by omega⟩
    let active : Finset p.Loc := (E v j0).filter (fun ℓ => A ℓ = true)
    let priorities := active.image (p.priority τ (v, j0))
    have hneP : priorities.Nonempty := by
      rcases hne with ⟨ℓ, hℓ⟩
      exact ⟨p.priority τ (v, j0) ℓ, Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩⟩
    let q := priorities.min' hneP
    have hmem : ∃ ℓ, ℓ ∈ active ∧ p.priority τ (v, j0) ℓ = q :=
      Finset.mem_image.mp (Finset.min'_mem priorities hneP)
    have hchosen' : Classical.choose hmem = ℓ₀ := by
      simpa [active, priorities, q, j0] using hchosen
    rcases Classical.choose_spec hmem with ⟨hactive, hrank⟩
    rw [hchosen'] at hactive hrank
    refine ⟨(Finset.mem_filter.mp hactive).2, ?_⟩
    intro m hm hAm
    have hmActive : m ∈ active := by
      simp only [active, Finset.mem_filter]
      exact ⟨hm, hAm⟩
    calc
      p.priority τ (v, j0) ℓ₀ = q := hrank
      _ ≤ p.priority τ (v, j0) m :=
        Finset.min'_le priorities (p.priority τ (v, j0) m)
          (Finset.mem_image.mpr ⟨m, hmActive, rfl⟩)
  · simp [HDParams.selection, HDParams.selectionAt, hheight, hH] at hselect

/-- The height-zero event can only reduce the uniform eligible-center bound. -/
theorem selected_zero_probability_le_card_inv (p : HDParams)
    (P : p.Loc → Bool) (E : p.EligMap) (Sites : p.Sites)
    (v : CubeVertex p.d) (ℓ : p.Loc) (hℓ : ℓ ∈ E v ⟨0, by omega⟩) :
    (p.actLaw.prod p.tieLaw).pr (fun ω =>
      p.height Sites P ω.1 E p.Rlong v = 0 ∧
        p.selection Sites P ω.1 E ω.2 v = some ℓ) ≤
      ((E v ⟨0, by omega⟩).card : ℝ)⁻¹ := by
  exact (finProb_pr_mono (p.actLaw.prod p.tieLaw) _ _
    (fun ω h => selected_zero_is_min p Sites P ω.1 E ω.2 v ℓ h.1 h.2)).trans
      (tieMin_probability_le_inv p (E v ⟨0, by omega⟩) (v, ⟨0, by omega⟩) ℓ hℓ)

/-- The `.99λ` gate yields the sharp weight needed when multiplying m external slices. -/
theorem selected_zero_probability_le (p : HDParams) (hlam : 0 < p.lam)
    (P : p.Loc → Bool) (E : p.EligMap) (Sites : p.Sites)
    (v : CubeVertex p.d) (ℓ : p.Loc) (hℓ : ℓ ∈ E v ⟨0, by omega⟩)
    (hsize : (99 / 100 : ℝ) * p.lam ≤ ((E v ⟨0, by omega⟩).card : ℝ)) :
    (p.actLaw.prod p.tieLaw).pr (fun ω =>
      p.height Sites P ω.1 E p.Rlong v = 0 ∧
        p.selection Sites P ω.1 E ω.2 v = some ℓ) ≤
      1 / ((99 / 100 : ℝ) * p.lam) := by
  apply (selected_zero_probability_le_card_inv p P E Sites v ℓ hℓ).trans
  rw [← one_div]
  apply one_div_le_one_div_of_le
  · positivity
  · exact hsize


/-! Taking position-dependent suprema does not weaken uniform selector estimates. -/

private theorem expect_mono {α : Type*} [Fintype α] (P : FinProb α)
    {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : P.expect f ≤ P.expect g := by
  unfold FinProb.expect
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (P.nonneg a)

private theorem pr_prod_eq_expect {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (F : α → β → Prop) :
    (P.prod Q).pr (fun ω => F ω.1 ω.2) = P.expect (fun a => Q.pr (F a)) := by
  classical
  unfold FinProb.pr FinProb.expect FinProb.prod
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : F a b <;> simp [h]

private theorem pr_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (F : α → Prop) :
    (P.prod Q).pr (fun ω => F ω.1) = P.pr F := by
  classical
  rw [pr_prod_eq_expect P Q (fun a _ => F a)]
  unfold FinProb.expect FinProb.pr
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : F a <;> simp [h, Q.sum_eq_one]

/-- A uniform estimate for every position-dependent finite selector also bounds its supremum. -/
theorem expect_finite_sup_le {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (P : FinProb α) (f : α → β → ℝ) (B : ℝ)
    (hbound : ∀ C : α → β, P.expect (fun a => f a (C a)) ≤ B) :
    P.expect (fun a => ⨆ b, f a b) ≤ B := by
  classical
  have hmax (a : α) : ∃ b, ∀ b', f a b' ≤ f a b := by
    obtain ⟨b, hb, hm⟩ := Finset.exists_max_image Finset.univ (f a) Finset.univ_nonempty
    exact ⟨b, fun b' => hm b' (Finset.mem_univ b')⟩
  choose C hC using hmax
  apply (expect_mono P (fun a => ?_)).trans (hbound C)
  exact ciSup_le (hC a)

/-- Probability of a higher-level choice, maximized over legal eligibility maps. -/
noncomputable def positiveSelectionCap (p : HDParams) (Sites : p.Sites)
    (v : CubeVertex p.d) (ℓ : p.Loc) (P : p.Loc → Bool) : ℝ :=
  ⨆ E : p.EligMap, (p.actLaw.prod p.tieLaw).pr (fun ω =>
    p.Legal P E (p.domBall Sites v p.Rlong) ∧
    0 < p.height Sites P ω.1 E p.Rlong v ∧
    p.selection Sites P ω.1 E ω.2 v = some ℓ)

/-- The finite supremum depends only on positions and inherits the forced-center height bound. -/
theorem positiveSelectionCap_mean_le (p : HDParams) (Sites : p.Sites)
    (v : CubeVertex p.d) (ℓ : p.Loc) (pos : FinProb (p.Loc → Bool)) (ε : ℝ)
    (hbound : ∀ Esel : (p.Loc → Bool) → p.EligMap,
      (pos.prod p.actLaw).pr (fun ω =>
        p.Legal ω.1 (Esel ω.1) (p.domBall Sites v p.Rlong) ∧
        0 < p.height Sites ω.1 ω.2 (Esel ω.1) p.Rlong v) ≤ ε) :
    pos.expect (positiveSelectionCap p Sites v ℓ) ≤ ε := by
  classical
  unfold positiveSelectionCap
  apply expect_finite_sup_le
  intro Esel
  calc
    _ ≤ pos.expect (fun P => p.actLaw.pr (fun A =>
      p.Legal P (Esel P) (p.domBall Sites v p.Rlong) ∧
      0 < p.height Sites P A (Esel P) p.Rlong v)) := by
        apply expect_mono
        intro P
        have hmono := finProb_pr_mono (p.actLaw.prod p.tieLaw)
          (fun ω => p.Legal P (Esel P) (p.domBall Sites v p.Rlong) ∧
            0 < p.height Sites P ω.1 (Esel P) p.Rlong v ∧
            p.selection Sites P ω.1 (Esel P) ω.2 v = some ℓ)
          (fun ω => p.Legal P (Esel P) (p.domBall Sites v p.Rlong) ∧
            0 < p.height Sites P ω.1 (Esel P) p.Rlong v)
          (fun ω h => ⟨h.1, h.2.1⟩)
        rwa [pr_prod_fst p.actLaw p.tieLaw (fun A =>
          p.Legal P (Esel P) (p.domBall Sites v p.Rlong) ∧
          0 < p.height Sites P A (Esel P) p.Rlong v)] at hmono
    _ ≤ ε := by
      rw [← pr_prod_eq_expect]
      exact hbound Esel

private theorem selection_spec_of_some {p : HDParams}
    (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties)
    (v : CubeVertex p.d) (ℓ : p.Loc)
    (hsel : p.selection Sites P A E τ v = some ℓ) :
    ∃ j : Fin (p.H + 1),
      p.height Sites P A E p.Rlong v = j.val ∧ j.val < p.H ∧
        ¬ p.Bad P A E v j ∧ ℓ ∈ E v j ∧ A ℓ = true := by
  classical
  let h := p.height Sites P A E p.Rlong v
  have hh : h < p.H := by
    by_contra hnot
    simp [HDParams.selection, HDParams.selectionAt, h, hnot] at hsel
  let j : Fin (p.H + 1) := ⟨h, by omega⟩
  have hbad : ¬ p.Bad P A E v j := by
    intro hbad
    simp [HDParams.selection, HDParams.selectionAt, h, hh, j, hbad] at hsel
  have hsel' := hsel
  simp [HDParams.selection, HDParams.selectionAt, h, hh, j, hbad] at hsel'
  rcases hsel' with ⟨hne, hchosen⟩
  let active : Finset p.Loc := (E v j).filter (fun x => A x = true)
  let priorities := active.image (p.priority τ (v, j))
  have hneP : priorities.Nonempty := by
    rcases hne with ⟨x, hx⟩
    exact ⟨p.priority τ (v, j) x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  let q := priorities.min' hneP
  have hmem : ∃ x, x ∈ active ∧ p.priority τ (v, j) x = q := by
    obtain ⟨x, hx⟩ := Finset.mem_image.mp (Finset.min'_mem priorities hneP)
    exact ⟨x, hx.1, hx.2⟩
  have hchosen' : Classical.choose hmem = ℓ := by
    simpa [active, priorities, q, j] using hchosen
  obtain ⟨hactive, hpriority⟩ := Classical.choose_spec hmem
  rw [hchosen'] at hactive
  have hfilter := Finset.mem_filter.mp hactive
  refine ⟨j, rfl, hh, hbad, hfilter.1, ?_⟩
  simpa using hfilter.2


private theorem selection_level_of_legal (p : HDParams)
    (Sites : p.Sites) (v : CubeVertex p.d) (hv : v ∈ Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties) (ℓ : p.Loc)
    (hlegal : p.Legal P E (p.domBall Sites v p.Rlong))
    (hsel : p.selection Sites P A E τ v = some ℓ) :
    ℓ.2.val = p.height Sites P A E p.Rlong v ∧ ℓ ∈ E v ℓ.2 := by
  have hvdom : v ∈ p.domBall Sites v p.Rlong := by simp [HDParams.domBall, hv]
  obtain ⟨j, hh, _, _, hmem, _⟩ := selection_spec_of_some Sites P A E τ v ℓ hsel
  have hj : ℓ.2 = j := ((hlegal v hvdom j).1 ℓ hmem).2.1
  exact ⟨(congrArg Fin.val hj).trans hh.symm, hj.symm ▸ hmem⟩

/-- Eligibility-free activation/tie weight, including the size and consultation gates. -/
noncomputable def selectionCap (p : HDParams) (Sites : p.Sites)
    (v : CubeVertex p.d) (ℓ : p.Loc) (P : p.Loc → Bool) : ℝ :=
  ⨆ E : p.EligMap, (p.actLaw.prod p.tieLaw).pr (fun ω =>
    (∀ j, (99 / 100 : ℝ) * p.lam ≤ ((E v j).card : ℝ)) ∧
    p.Legal P E (p.domBall Sites v p.Rlong) ∧
    p.selection Sites P ω.1 E ω.2 v = some ℓ)

/-- A specified legal eligibility map is dominated by the position-only cap. -/
theorem selection_probability_le_cap (p : HDParams) (Sites : p.Sites)
    (v : CubeVertex p.d) (ℓ : p.Loc) (P : p.Loc → Bool) (E : p.EligMap) :
    (p.actLaw.prod p.tieLaw).pr (fun ω =>
      (∀ j, (99 / 100 : ℝ) * p.lam ≤ ((E v j).card : ℝ)) ∧
      p.Legal P E (p.domBall Sites v p.Rlong) ∧
      p.selection Sites P ω.1 E ω.2 v = some ℓ) ≤
        selectionCap p Sites v ℓ P := by
  unfold selectionCap
  apply le_ciSup ?_ E
  exact (Set.finite_range _).bddAbove

/-- At level zero the position-only cap costs at most 1/(.99λ). -/
theorem selectionCap_zero_le (p : HDParams) (hlam : 0 < p.lam)
    (Sites : p.Sites) (v : CubeVertex p.d) (hv : v ∈ Sites)
    (ℓ : p.Loc) (hlevel : ℓ.2.val = 0) (P : p.Loc → Bool) :
    selectionCap p Sites v ℓ P ≤ 1 / ((99 / 100 : ℝ) * p.lam) := by
  classical
  unfold selectionCap
  apply ciSup_le
  intro E
  by_cases hsize : ∀ j, (99 / 100 : ℝ) * p.lam ≤ ((E v j).card : ℝ)
  · by_cases hlegal : p.Legal P E (p.domBall Sites v p.Rlong)
    · have hzero : ℓ.2 = (⟨0, by omega⟩ : Fin (p.H + 1)) := Fin.ext hlevel
      by_cases hmem : ℓ ∈ E v ⟨0, by omega⟩
      · apply (finProb_pr_mono (p.actLaw.prod p.tieLaw) _
          (fun ω => p.height Sites P ω.1 E p.Rlong v = 0 ∧
            p.selection Sites P ω.1 E ω.2 v = some ℓ) ?_).trans
          (selected_zero_probability_le p hlam P E Sites v ℓ hmem (hsize _))
        intro ω h
        have hh := (selection_level_of_legal p Sites v hv P ω.1 E ω.2 ℓ hlegal h.2.2).1
        exact ⟨hh.symm.trans hlevel, h.2.2⟩
      · have hfalse (ω : (p.Loc → Bool) × p.Ties) :
          ¬ ((∀ j, (99 / 100 : ℝ) * p.lam ≤ ((E v j).card : ℝ)) ∧
            p.Legal P E (p.domBall Sites v p.Rlong) ∧
            p.selection Sites P ω.1 E ω.2 v = some ℓ) := by
          intro h
          have hm := (selection_level_of_legal p Sites v hv P ω.1 E ω.2 ℓ hlegal h.2.2).2
          exact hmem (hzero ▸ hm)
        simp only [FinProb.pr, ite_eq_right (hfalse _), Finset.sum_const_zero]
        positivity
    · simp [FinProb.pr, hlegal, le_of_lt hlam]
  · simp [FinProb.pr, hsize, le_of_lt hlam]

/-- Higher-level choice caps are bounded by the position-only positive-height cap. -/
theorem selectionCap_pos_le (p : HDParams) (Sites : p.Sites)
    (v : CubeVertex p.d) (hv : v ∈ Sites) (ℓ : p.Loc) (hlevel : 0 < ℓ.2.val)
    (P : p.Loc → Bool) :
    selectionCap p Sites v ℓ P ≤ positiveSelectionCap p Sites v ℓ P := by
  classical
  unfold selectionCap positiveSelectionCap
  apply ciSup_le
  intro E
  have hsup : (p.actLaw.prod p.tieLaw).pr (fun ω =>
      p.Legal P E (p.domBall Sites v p.Rlong) ∧
      0 < p.height Sites P ω.1 E p.Rlong v ∧
      p.selection Sites P ω.1 E ω.2 v = some ℓ) ≤
      ⨆ E' : p.EligMap, (p.actLaw.prod p.tieLaw).pr (fun ω =>
        p.Legal P E' (p.domBall Sites v p.Rlong) ∧
        0 < p.height Sites P ω.1 E' p.Rlong v ∧
        p.selection Sites P ω.1 E' ω.2 v = some ℓ) := by
    apply le_ciSup ?_ E
    exact (Set.finite_range _).bddAbove
  apply (finProb_pr_mono (p.actLaw.prod p.tieLaw) _
    (fun ω => p.Legal P E (p.domBall Sites v p.Rlong) ∧
      0 < p.height Sites P ω.1 E p.Rlong v ∧
      p.selection Sites P ω.1 E ω.2 v = some ℓ) ?_).trans
    hsup
  intro ω h
  have hh := (selection_level_of_legal p Sites v hv P ω.1 E ω.2 ℓ h.2.1 h.2.2).1
  exact ⟨h.2.1, hh ▸ hlevel, h.2.2⟩


/-! Forced-present averaging for the position field. -/

private theorem position_force_weight (p : HDParams) (ℓ : p.Loc)
    (hq0 : 0 ≤ p.lam / (p.V : ℝ)) (hq1 : p.lam / (p.V : ℝ) ≤ 1)
    (P : p.Loc → Bool) :
    (if P ℓ = true then p.posLaw.w P else 0) =
      (p.lam / (p.V : ℝ)) * (p.posLawForced (some ℓ)).w P := by
  classical
  let q := p.lam / (p.V : ℝ)
  let f : p.Loc → ℝ := fun x => (FinProb.bernoulli q).w (P x)
  let g : p.Loc → ℝ := fun x =>
    (if some ℓ = some x then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P x)
  have herase : (∏ x ∈ Finset.univ.erase ℓ, g x) =
      ∏ x ∈ Finset.univ.erase ℓ, f x := by
    apply Finset.prod_congr rfl
    intro x hx
    have hne : x ≠ ℓ := (Finset.mem_erase.mp hx).1
    simp [f, g, Ne.symm hne]
  have hplain : p.posLaw.w P = f ℓ * ∏ x ∈ Finset.univ.erase ℓ, f x := by
    exact (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ ℓ)).symm
  have hforced : (p.posLawForced (some ℓ)).w P =
      g ℓ * ∏ x ∈ Finset.univ.erase ℓ, f x := by
    change (∏ x, g x) = _
    rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ ℓ), herase]
  rw [hplain, hforced]
  cases hP : P ℓ <;> simp [f, g, FinProb.bernoulli, hP,
    max_eq_right hq0, min_eq_left hq1, q]

/-- Requiring one named center to be present costs λ/V; all other positions keep their law. -/
theorem position_expect_force_present (p : HDParams) (ℓ : p.Loc)
    (hq0 : 0 ≤ p.lam / (p.V : ℝ)) (hq1 : p.lam / (p.V : ℝ) ≤ 1)
    (f : (p.Loc → Bool) → ℝ) :
    p.posLaw.expect (fun P => if P ℓ = true then f P else 0) =
      (p.lam / (p.V : ℝ)) * (p.posLawForced (some ℓ)).expect f := by
  classical
  unfold FinProb.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  have hw := position_force_weight p ℓ hq0 hq1 P
  calc
    p.posLaw.w P * (if P ℓ = true then f P else 0) =
        (if P ℓ = true then p.posLaw.w P else 0) * f P := by
          split_ifs <;> simp
    _ = (p.lam / (p.V : ℝ)) * (p.posLawForced (some ℓ)).w P * f P := by rw [hw]
    _ = _ := by ring


private theorem pr_nonneg {α : Type*} [Fintype α] (P : FinProb α) (F : α → Prop) :
    0 ≤ P.pr F := by
  classical
  unfold FinProb.pr
  apply Finset.sum_nonneg
  intro a ha
  split_ifs <;> simp [P.nonneg]

/-- Every position-only selection cap is nonnegative. -/
theorem selectionCap_nonneg (p : HDParams) (Sites : p.Sites)
    (v : CubeVertex p.d) (ℓ : p.Loc) (P : p.Loc → Bool) :
    0 ≤ selectionCap p Sites v ℓ P := by
  exact (pr_nonneg (p.actLaw.prod p.tieLaw) _).trans
    (selection_probability_le_cap p Sites v ℓ P (fun _ _ => ∅))

/-- An absent center, or a location outside the queried ball, has zero cap. -/
theorem selectionCap_eq_zero_of_not_position (p : HDParams) (Sites : p.Sites)
    (v : CubeVertex p.d) (hv : v ∈ Sites) (ℓ : p.Loc) (P : p.Loc → Bool)
    (hnot : ¬ (P ℓ = true ∧ _root_.hammingDist ℓ.1 v ≤ p.r)) :
    selectionCap p Sites v ℓ P = 0 := by
  classical
  apply le_antisymm _ (selectionCap_nonneg p Sites v ℓ P)
  unfold selectionCap
  apply ciSup_le
  intro E
  have hvdom : v ∈ p.domBall Sites v p.Rlong := by simp [HDParams.domBall, hv]
  have hfalse (ω : (p.Loc → Bool) × p.Ties) :
      ¬ ((∀ j, (99 / 100 : ℝ) * p.lam ≤ ((E v j).card : ℝ)) ∧
        p.Legal P E (p.domBall Sites v p.Rlong) ∧
        p.selection Sites P ω.1 E ω.2 v = some ℓ) := by
    intro h
    have hm := (selection_level_of_legal p Sites v hv P ω.1 E ω.2 ℓ h.2.1 h.2.2).2
    have hspec := ((h.2.1 v hvdom ℓ.2).1 ℓ hm)
    exact hnot ⟨hspec.1, hspec.2.2⟩
  simp only [FinProb.pr, ite_eq_right (hfalse _), Finset.sum_const_zero, le_refl]

/-- Without forcing, each cap pays the probability that its named center is present. -/
theorem selectionCap_mean_eq_forced (p : HDParams) (Sites : p.Sites)
    (v : CubeVertex p.d) (hv : v ∈ Sites) (ℓ : p.Loc)
    (hq0 : 0 ≤ p.lam / (p.V : ℝ)) (hq1 : p.lam / (p.V : ℝ) ≤ 1) :
    p.posLaw.expect (selectionCap p Sites v ℓ) =
      (p.lam / (p.V : ℝ)) *
        (p.posLawForced (some ℓ)).expect (selectionCap p Sites v ℓ) := by
  classical
  have heq (P : p.Loc → Bool) : selectionCap p Sites v ℓ P =
      if P ℓ = true then selectionCap p Sites v ℓ P else 0 := by
    split_ifs with hP
    · rfl
    · exact selectionCap_eq_zero_of_not_position p Sites v hv ℓ P (fun h => hP h.1)
  calc
    _ = p.posLaw.expect (fun P => if P ℓ = true then selectionCap p Sites v ℓ P else 0) :=
      congrArg p.posLaw.expect (funext heq)
    _ = _ := position_expect_force_present p ℓ hq0 hq1 _

/-- A level-zero center's expected weight is at most 1/(.99V). -/
theorem selectionCap_zero_mean_le (p : HDParams) (hlam : 0 < p.lam)
    (Sites : p.Sites) (v : CubeVertex p.d) (hv : v ∈ Sites)
    (ℓ : p.Loc) (hlevel : ℓ.2.val = 0)
    (hq1 : p.lam / (p.V : ℝ) ≤ 1) :
    p.posLaw.expect (selectionCap p Sites v ℓ) ≤
      (p.lam / (p.V : ℝ)) * (1 / ((99 / 100 : ℝ) * p.lam)) := by
  have hq0 : 0 ≤ p.lam / (p.V : ℝ) := div_nonneg hlam.le (Nat.cast_nonneg _)
  rw [selectionCap_mean_eq_forced p Sites v hv ℓ hq0 hq1]
  apply mul_le_mul_of_nonneg_left _ hq0
  calc
    _ ≤ (p.posLawForced (some ℓ)).expect (fun _ => 1 / ((99 / 100 : ℝ) * p.lam)) :=
      expect_mono _ (fun P => selectionCap_zero_le p hlam Sites v hv ℓ hlevel P)
    _ = _ := by simp [FinProb.expect, ← Finset.sum_mul, FinProb.sum_eq_one]

/-- Higher-level named centers pay λ/V times the forced-center positive-height bound. -/
theorem selectionCap_positive_mean_le (p : HDParams) (Sites : p.Sites)
    (v : CubeVertex p.d) (hv : v ∈ Sites) (ℓ : p.Loc) (hlevel : 0 < ℓ.2.val)
    (hq0 : 0 ≤ p.lam / (p.V : ℝ)) (hq1 : p.lam / (p.V : ℝ) ≤ 1) (ε : ℝ)
    (hbound : ∀ Esel : (p.Loc → Bool) → p.EligMap,
      ((p.posLawForced (some ℓ)).prod p.actLaw).pr (fun ω =>
        p.Legal ω.1 (Esel ω.1) (p.domBall Sites v p.Rlong) ∧
        0 < p.height Sites ω.1 ω.2 (Esel ω.1) p.Rlong v) ≤ ε) :
    p.posLaw.expect (selectionCap p Sites v ℓ) ≤ (p.lam / (p.V : ℝ)) * ε := by
  rw [selectionCap_mean_eq_forced p Sites v hv ℓ hq0 hq1]
  apply mul_le_mul_of_nonneg_left _ hq0
  exact (expect_mono _ (fun P => selectionCap_pos_le p Sites v hv ℓ hlevel P)).trans
    (positiveSelectionCap_mean_le p Sites v ℓ (p.posLawForced (some ℓ)) ε hbound)


/-! Independent fields can be regrouped into one experiment per slice. -/

/-- Expectation of a product of functions of independent coordinates factors. -/
theorem pi_expect_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (f : ∀ i, Ω i → ℝ) :
    (FinProb.pi P).expect (fun ω => ∏ i, f i (ω i)) = ∏ i, (P i).expect (f i) := by
  classical
  unfold FinProb.expect FinProb.pi
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (P i).w a * f i a)).symm

/-- A product field indexed by slice-center pairs equals a product of per-slice fields. -/
theorem pi_curry_expect {ι κ Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype Ω]
    (P : ι → κ → FinProb Ω) (f : (ι → κ → Ω) → ℝ) :
    (FinProb.pi (fun x : ι × κ => P x.1 x.2)).expect
      (fun ω => f (fun i j => ω (i, j))) =
      (FinProb.pi (fun i => FinProb.pi (P i))).expect f := by
  classical
  let e : (ι → κ → Ω) ≃ (ι × κ → Ω) :=
    { toFun := fun ω x => ω x.1 x.2
      invFun := fun ω i j => ω (i, j)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold FinProb.expect FinProb.pi
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro ω hω
  change (∏ x : ι × κ, (P x.1 x.2).w (ω x.1 x.2)) * f ω =
    (∏ i, ∏ j, (P i j).w (ω i j)) * f ω
  rw [Fintype.prod_prod_type]

/-- Independent activation and tie fields can be paired separately at every slice. -/
theorem pi_pair_expect {ι Ω Ψ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Ψ]
    (P : ι → FinProb Ω) (Q : ι → FinProb Ψ)
    (f : (ι → Ω) × (ι → Ψ) → ℝ) :
    ((FinProb.pi P).prod (FinProb.pi Q)).expect f =
      (FinProb.pi (fun i => (P i).prod (Q i))).expect
        (fun ω => f ((fun i => (ω i).1), (fun i => (ω i).2))) := by
  classical
  let e : (ι → Ω × Ψ) ≃ ((ι → Ω) × (ι → Ψ)) :=
    { toFun := fun ω => (fun i => (ω i).1, fun i => (ω i).2)
      invFun := fun ω i => (ω.1 i, ω.2 i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold FinProb.expect FinProb.pi FinProb.prod
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro ω hω
  change (∏ i, (P i).w (ω i).1) * (∏ i, (Q i).w (ω i).2) *
      f ((fun i => (ω i).1), (fun i => (ω i).2)) =
    (∏ i, (P i).w (ω i).1 * (Q i).w (ω i).2) *
      f ((fun i => (ω i).1), (fun i => (ω i).2))
  rw [Finset.prod_mul_distrib]


/-- An independent one-point auxiliary field does not change event probability. -/
theorem pr_prod_unit_middle {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (F : α → β → Prop) :
    ((P.prod (FinProb.uniformAll (Ω := Unit) ⟨()⟩)).prod Q).pr
      (fun ω => F ω.1.1 ω.2) = (P.prod Q).pr (fun ω => F ω.1 ω.2) := by
  classical
  simp [FinProb.pr, FinProb.prod, FinProb.uniformAll, Fintype.sum_prod_type]

end HypercubeRamsey.Lane_sol_s10_d56
