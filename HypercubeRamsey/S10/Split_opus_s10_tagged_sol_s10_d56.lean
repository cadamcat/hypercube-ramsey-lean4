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

end HypercubeRamsey.Lane_sol_s10_d56
