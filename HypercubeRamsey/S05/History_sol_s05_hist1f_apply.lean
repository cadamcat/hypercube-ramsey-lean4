import HypercubeRamsey.S05.History_sol_s05_hist1f

namespace HypercubeRamsey.Lane_sol_s05_hist1b

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

/-- The reference set of a low record is fixed before arrays are sampled. -/
def lowRefs (r : X.AbsRecord) : Finset (Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound)) :=
  r.2.2.1.image fun c => (c.1, c.2.1,
    Finset.univ.filter fun i : Fin X.blockBound => (i : ℕ) < X.p.typeBlocks n c.2.1)

theorem low_record_ref_mode (r : X.AbsRecord) (hr : X.RecOccurs r) (hl : r.1.isLeft)
    (c : Fin (X.p.T n) × X.Ty × Option X.Key) (hc : c ∈ r.2.2.1) :
    c.2.1.2.2.isSome := by
  letI : DecidableEq (Fin (X.p.T n)) := Classical.decEq _
  obtain ⟨y, μ, _, _, href, _⟩ := hr
  rw [href] at hc
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hc
  have hmode := (Finset.mem_filter.mp ha).2.2
  have hproj : (X.g.evenType (X.p.J n) a.1).2.2.isSome = c.2.1.2.2.isSome :=
    congrArg (fun d => d.2.1.2.2.isSome) he
  exact hproj.symm.trans (hmode.symm.trans hl)

theorem refsOn_low (H : X.KeyHist) (r : X.AbsRecord) (hr : X.RecOccurs r)
    (hl : r.1.isLeft) (a : X.ArraysOn (Fin (X.p.T n))) :
    X.refsOn H r a = lowRefs X r := by
  unfold Setup5.refsOn lowRefs
  apply Finset.image_congr
  intro c hc
  have hm := low_record_ref_mode X r hr hl c hc
  cases he : c.2.1.2.2 with
  | none => simp [he] at hm
  | some j => simp [Setup5.refSubsetOn, he]

/-- The full low-target union bound in the raw target-and-array law. -/
theorem step3_low_finite_bound (H : X.KeyHist) (r : X.AbsRecord) (hr : X.RecOccurs r)
    (hl : r.1.isLeft) (ε : ℝ) (hε : 0 ≤ ε)
    (hlo : (match r.1 with
      | .inl k => Real.exp (-(X.p.delta * X.p.kPrime n k.2.2.val))
      | .inr _ => Real.exp (-(X.p.delta * X.p.s n))) ≤ ε)
    (href : ∀ c ∈ lowRefs X r,
      Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) ≤ ε) :
    (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
      (∏ h, (X.prior H.1 r.1).w (θ h)) * X.step3Rate (X.withCol H r.1 θ) r) ≤
      ((lowRefs X r).card + 1 : ℕ) * ε := by
  let P := FinProb.pi fun _ : Fin (colLen5 (X.p.s n) r.1) => X.prior H.1 r.1
  let Q := FinProb.bind P (fun θ => X.recArrayLaw (X.withCol H r.1 θ))
  let lower : (Fin (colLen5 (X.p.s n) r.1) → Fin N) × X.ArraysOn (Fin (X.p.T n)) → Prop :=
    fun ta => X.candGateOn (X.withCol H r.1 ta.1) r ta.2 ta.1 ∧
      X.step3MassOn (X.withCol H r.1 ta.1) r ta.2 none < ε
  let ratio (c : {c // c ∈ lowRefs X r}) := fun ta :
      (Fin (colLen5 (X.p.s n) r.1) → Fin N) × X.ArraysOn (Fin (X.p.T n)) =>
    X.candGateOn (X.withCol H r.1 ta.1) r ta.2 ta.1 ∧
      X.step3MassOn (X.withCol H r.1 ta.1) r ta.2 none <
        ε * X.step3MassOn (X.withCol H r.1 ta.1) r ta.2 (some c.1)
  have hpr (A : (Fin (colLen5 (X.p.s n) r.1) → Fin N) × X.ArraysOn (Fin (X.p.T n)) → Prop) :
      Q.pr A = ∑ θ, P.w θ * (X.recArrayLaw (X.withCol H r.1 θ)).pr (fun a => A (θ, a)) := by
    unfold FinProb.pr Q
    simp only [FinProb.bind, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro θ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have hlow : Q.pr lower ≤ ε := by
    rw [hpr]
    exact step3_lower_tail X H r hr ε hε
  have hratio (c : {c // c ∈ lowRefs X r}) : Q.pr (ratio c) ≤ ε := by
    rw [hpr]
    exact step3_fixed_ratio_tail X H r hr c.1 ε hε
  have hfail : ∀ ta, X.step3FailOn (X.withCol H r.1 ta.1) r ta.2 →
      lower ta ∨ ∃ c, ratio c ta := by
    intro ta hf
    have ht : (X.withCol H r.1 ta.1).2 r.1 = ta.1 := by simp [Setup5.withCol]
    rw [Setup5.step3FailOn, ht] at hf
    obtain ⟨hg, hm | hm | hm⟩ := hf
    · exact Or.inl ⟨hg, hm.trans_le hlo⟩
    · obtain ⟨c, hc, hb⟩ := hm
      rw [refsOn_low X _ r hr hl] at hc
      refine Or.inr ⟨⟨c, hc⟩, hg, hb.trans_le ?_⟩
      exact mul_le_mul_of_nonneg_right (href c hc) (step3MassOn_nonneg X _ r ta.2 (some c))
    · have hn : ¬ r.1.isRight := by
        cases h : r.1 with
        | inl k => simp [h]
        | inr k => simp [h] at hl
      exact False.elim (hn hm.1)
  have heq : (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
      (∏ h, (X.prior H.1 r.1).w (θ h)) * X.step3Rate (X.withCol H r.1 θ) r) =
      Q.pr (fun ta => X.step3FailOn (X.withCol H r.1 ta.1) r ta.2) := by
    rw [hpr]
    rfl
  rw [heq]
  calc
    _ ≤ Q.pr (fun ta => lower ta ∨ ∃ c, ratio c ta) := by
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro ta _
      by_cases hf : X.step3FailOn (X.withCol H r.1 ta.1) r ta.2
      · simp only [if_pos hf, if_pos (hfail ta hf)]
        exact le_refl _
      · simp only [if_neg hf]
        split_ifs <;> simp [Q.nonneg ta]
    _ ≤ Q.pr lower + Q.pr (fun ta => ∃ c, ratio c ta) := Q.pr_union _ _
    _ ≤ ε + ∑ c, Q.pr (ratio c) := add_le_add hlow (FinProb.pr_exists_le_sum5 Q ratio)
    _ ≤ ε + ∑ _c : {c // c ∈ lowRefs X r}, ε :=
      add_le_add (le_refl _) (Finset.sum_le_sum fun c _ => hratio c)
    _ = _ := by simp; ring

end
end HypercubeRamsey.Lane_sol_s05_hist1b
