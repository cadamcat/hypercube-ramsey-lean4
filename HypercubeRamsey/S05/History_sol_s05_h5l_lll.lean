import HypercubeRamsey.S05.History_sol_s05_h5l_avoid
import HypercubeRamsey.S03.ConditionalAvoidance

namespace HypercubeRamsey.Lane_sol_s05_h5l

open Classical

noncomputable section
set_option maxHeartbeats 800000

variable {V A I : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I]

def resample (P : V → FinProb A) (Λ : Finset V) (z : V → A) : FinProb (V → A) :=
  FinProb.pi fun v => if v ∈ Λ then P v else Lane_q_s05_h5l.pinDirac5 (z v)

private theorem pi_split (P : V → FinProb A) (Λ : Finset V) (F : (V → A) → ℝ) :
    (FinProb.pi P).expect F =
      ∑ b : ({v : V // v ∉ Λ} → A), (FinProb.pi (fun v : {v : V // v ∉ Λ} => P v.1)).w b *
        (FinProb.pi (fun v : Λ => P v.1)).expect
          (fun a => F ((Equiv.piEquivPiSubtypeProd (fun v => v ∈ Λ) (fun _ => A)).symm (a, b))) := by
  let e := Equiv.piEquivPiSubtypeProd (fun v => v ∈ Λ) (fun _ => A)
  unfold FinProb.expect
  rw [← Equiv.sum_comp e.symm (fun z => (FinProb.pi P).w z * F z), Fintype.sum_prod_type,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hw : (FinProb.pi P).w (e.symm (a, b)) =
      (FinProb.pi (fun v : Λ => P v.1)).w a *
        (FinProb.pi (fun v : {v : V // v ∉ Λ} => P v.1)).w b := by
    simp only [FinProb.pi]
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun v => v ∈ Λ)]
    congr 1
    · apply Finset.prod_congr (by ext v; simp)
      intro v hv
      simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos v.2]
    · apply Finset.prod_congr (by ext v; simp)
      intro v hv
      simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg v.2]
  rw [hw]
  ring

/-- Constraints that read no resampled coordinates preserve a uniform resampling bound. -/
theorem untouched_resample_bound (P : V → FinProb A) (Λ : Finset V)
    (B : (V → A) → Prop) (hB : FinProb.DependsOn B (Finset.univ \ Λ))
    (F : (V → A) → ℝ) (M : ℝ) (z₀ : V → A)
    (hF : ∀ z, (resample P Λ z).expect F ≤ M) :
    (FinProb.pi P).expect (fun z => if B z then F z else 0) ≤ M * (FinProb.pi P).pr B := by
  let e := Equiv.piEquivPiSubtypeProd (fun v => v ∈ Λ) (fun _ => A)
  let a₀ : Λ → A := fun v => z₀ v.1
  let Pc := FinProb.pi (fun v : {v : V // v ∉ Λ} => P v.1)
  let Ps := FinProb.pi (fun v : Λ => P v.1)
  have hBsame (a : Λ → A) (b : {v : V // v ∉ Λ} → A) :
      B (e.symm (a, b)) = B (e.symm (a₀, b)) := by
    apply hB
    intro v hv
    have hv' : v ∉ Λ := (Finset.mem_sdiff.mp hv).2
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, hv']
  have hR (b : {v : V // v ∉ Λ} → A) :
      Ps.expect (fun a => F (e.symm (a, b))) ≤ M := by
    have h := hF (e.symm (a₀, b))
    rw [resample, Lane_q_s05_h5l.pi_expect_pinned5] at h
    convert h using 1
    congr 1
    funext a
    congr 1
    funext v
    by_cases hv : v ∈ Λ <;> simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, hv]
  have hPr : (FinProb.pi P).pr B = ∑ b, if B (e.symm (a₀, b)) then Pc.w b else 0 := by
    have hIndicator : (FinProb.pi P).pr B =
        (FinProb.pi P).expect (fun z => if B z then (1 : ℝ) else 0) := by
      simp [FinProb.pr, FinProb.expect, mul_ite]
    rw [hIndicator, pi_split]
    apply Finset.sum_congr rfl
    intro b hb
    change Pc.w b * Ps.expect _ = _
    change Pc.w b * (∑ a, Ps.w a * (if B (e.symm (a, b)) then (1 : ℝ) else 0)) = _
    simp_rw [hBsame]
    by_cases hbb : B (e.symm (a₀, b))
    · simp [hbb, FinProb.expect, Ps.sum_eq_one]
    · simp [hbb, FinProb.expect]
  rw [hPr, Finset.mul_sum, pi_split]
  apply Finset.sum_le_sum
  intro b hb
  change Pc.w b * Ps.expect _ ≤ _
  change Pc.w b * (∑ a, Ps.w a * (if B (e.symm (a, b)) then F (e.symm (a, b)) else 0)) ≤ _
  simp_rw [hBsame]
  by_cases hbb : B (e.symm (a₀, b))
  · simp only [if_pos hbb]
    simpa [FinProb.expect, mul_comm] using mul_le_mul_of_nonneg_left (hR b) (Pc.nonneg b)
  · simp [hbb, FinProb.expect]

private theorem mass_pr (P : FinProb (V → A)) (S : Finset (V → A)) :
    LocalLemma.mass P.w S = P.pr (fun z => z ∈ S) := by
  unfold LocalLemma.mass FinProb.pr
  calc
    (∑ z ∈ S, P.w z) = ∑ z, if z ∈ S then P.w z else 0 := (Finset.sum_ite_mem_eq S P.w).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      split_ifs <;> rfl

theorem resample_singleton_expect (P : V → FinProb A) (k : V) (z : V → A)
    (F : (V → A) → ℝ) :
    (resample P {k} z).expect F = (P k).expect (fun a => F (Function.update z k a)) := by
  let Q := fun v => if v ∈ ({k} : Finset V) then P v else Lane_q_s05_h5l.pinDirac5 (z v)
  have heq : (FinProb.pi Q).expect F =
      (FinProb.pi Q).expect (fun ω => F (Function.update z k (ω k))) := by
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases hw : (FinProb.pi Q).w ω = 0
    · simp [hw]
    · have hout (v : V) (hv : v ≠ k) : ω v = z v := by
        have hh := (Finset.prod_ne_zero_iff.mp hw) v (Finset.mem_univ _)
        by_contra hne
        exact hh (by simp [Q, hv, Lane_q_s05_h5l.pinDirac5, hne])
      have hupdate : Function.update z k (ω k) = ω := by
        funext v
        by_cases hv : v = k
        · subst v; simp
        · simp [Function.update_of_ne hv, hout v hv]
      change (FinProb.pi Q).w ω * F ω = (FinProb.pi Q).w ω * F (Function.update z k (ω k))
      rw [hupdate]
  change (FinProb.pi Q).expect F = _
  rw [heq, Lane_q_s05_h5l.pi_expect_singleton5 Q k
    (fun a => F (Function.update z k a)) (z k)]
  simp only [Q, Finset.mem_singleton_self, if_true]

/-- A one-coordinate bound at every fixing of the other coordinates bounds the product mean. -/
theorem pi_expect_update_bound (P : V → FinProb A) (k : V) (F : (V → A) → ℝ)
    (M : ℝ) (z₀ : V → A)
    (hF : ∀ z, (P k).expect (fun a => F (Function.update z k a)) ≤ M) :
    (FinProb.pi P).expect F ≤ M := by
  have hh := untouched_resample_bound P {k} (fun _ => True)
    (fun _ _ _ => rfl) F M z₀ (fun z => by rw [resample_singleton_expect]; exact hF z)
  simpa [FinProb.pr, (FinProb.pi P).sum_eq_one] using hh

private theorem cond_expect (P : FinProb (V → A)) (S : Finset (V → A))
    (h : 0 < P.pr (fun z => z ∈ S)) (W : (V → A) → ℝ) :
    (P.cond (fun z => z ∈ S) h).expect W =
      (∑ z ∈ S, P.w z * W z) / LocalLemma.mass P.w S := by
  rw [mass_pr]
  simp only [FinProb.expect, FinProb.cond, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  simp only [ite_mul, zero_mul]
  exact Finset.sum_ite_mem_eq S (fun z => P.w z * W z)

/-- A scoped local lemma gives precisely the resampling comparison needed in Stage 5. -/
theorem scoped_avoidance (P : V → FinProb A) (Bad : I → (V → A) → Prop)
    (scope : I → Finset V) (hscope : ∀ i, FinProb.DependsOn (Bad i) (scope i))
    (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hLLL : ∀ i, (FinProb.pi P).pr (Bad i) ≤
      x i * ∏ j ∈ Finset.univ.filter (fun j => i ≠ j ∧ ¬ Disjoint (scope i) (scope j)), (1 - x j))
    (hcost : ∀ Λ : Finset V,
      (∏ i ∈ Finset.univ.filter (fun i => ¬ Disjoint (scope i) Λ), (1 - x i))⁻¹ ≤ (2 : ℝ) ^ Λ.card)
    (z₀ : V → A) :
    ∃ Q : FinProb (V → A),
      (∀ z, Q.w z ≠ 0 → (FinProb.pi P).w z ≠ 0 ∧ ∀ i, ¬ Bad i z) ∧
      ∀ (Λ : Finset V) (W : (V → A) → ℝ) (M : ℝ), (∀ z, 0 ≤ W z) →
        (∀ z, (resample P Λ z).expect W ≤ M) → Q.expect W ≤ (2 : ℝ) ^ Λ.card * M := by
  let E : I → Finset (V → A) := fun i => Finset.univ.filter (Bad i)
  let adj : I → I → Prop := fun i j => i ≠ j ∧ ¬ Disjoint (scope i) (scope j)
  let P₀ := FinProb.pi P
  have hmem (i z) : z ∈ E i ↔ Bad i z := by simp [E]
  have hE : ∀ i z z', (∀ v ∈ scope i, z v = z' v) → (z ∈ E i ↔ z' ∈ E i) := by
    intro i z z' h
    simpa only [hmem] using (iff_of_eq (hscope i z z' h))
  have hind (i : I) (S : Finset I) (hi : i ∉ S) (hS : ∀ j ∈ S, ¬ adj i j) :
      LocalLemma.mass P₀.w (E i ∩ LocalLemma.avoid E S) ≤
        P₀.pr (Bad i) * LocalLemma.mass P₀.w (LocalLemma.avoid E S) := by
    have hdis : ∀ j ∈ S, Disjoint (scope i) (scope j) := by
      intro j hj
      by_contra hd
      exact hS j hj ⟨by intro he; subst j; exact hi hj, hd⟩
    have hh := LocalLemma.mass_inter_avoid_of_disjoint_scopes
      (fun v => (P v).w) (fun v => (P v).nonneg) (fun v => (P v).sum_eq_one)
      E scope hE i S hdis
    change LocalLemma.mass (fun z : V → A => ∏ v, (P v).w (z v)) _ ≤ _
    rw [hh]
    have hp : LocalLemma.mass P₀.w (E i) = P₀.pr (Bad i) := by
      rw [mass_pr]
      simp only [hmem]
    rw [show (fun z : V → A => ∏ v, (P v).w (z v)) = P₀.w from rfl, hp]
  have hmain := LocalLemma.conditional_avoidance P₀.w P₀.nonneg P₀.sum_eq_one E adj
    (fun i j h => ⟨Ne.symm h.1, fun hd => h.2 hd.symm⟩)
    (fun i h => h.1 rfl) (fun i => P₀.pr (Bad i)) x hind hx0 hx1 hLLL
  have hpos : 0 < P₀.pr (fun z => z ∈ LocalLemma.avoid E Finset.univ) := by
    rw [← mass_pr]
    exact hmain.1
  let Q := P₀.cond (fun z => z ∈ LocalLemma.avoid E Finset.univ) hpos
  refine ⟨Q, ?_, ?_⟩
  · intro z hz
    have hzA : z ∈ LocalLemma.avoid E Finset.univ := by
      by_contra h
      exact hz (by simp [Q, FinProb.cond, h])
    constructor
    · intro h
      change P₀.w z = 0 at h
      exact hz (by simp [Q, FinProb.cond, h])
    · intro i h
      have hh := (Finset.mem_filter.mp hzA).2 i (Finset.mem_univ _)
      exact hh ((hmem i z).2 h)
  · intro Λ W M hW hR
    let T := Finset.univ.filter fun i => ¬ Disjoint (scope i) Λ
    let S := Finset.univ \ T
    have hST : Disjoint S T := Finset.sdiff_disjoint
    have hUnion : S ∪ T = Finset.univ := Finset.sdiff_union_of_subset (Finset.subset_univ _)
    have hB : FinProb.DependsOn (fun z => z ∈ LocalLemma.avoid E S) (Finset.univ \ Λ) := by
      intro z z' hz
      apply propext
      simp only [LocalLemma.avoid, Finset.mem_filter, Finset.mem_univ, true_and]
      have hsame (i) (hi : i ∈ S) : Bad i z = Bad i z' := by
        apply hscope i
        intro v hv
        apply hz
        have hiT : i ∉ T := (Finset.mem_sdiff.mp hi).2
        have hdis : Disjoint (scope i) Λ := by simpa [T] using hiT
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact fun hvΛ => Finset.disjoint_left.mp hdis hv hvΛ
      constructor <;> intro h i hi <;> simpa only [hmem, hsame i hi] using h i hi
    have hpart := untouched_resample_bound P Λ
      (fun z => z ∈ LocalLemma.avoid E S) hB W M z₀ hR
    have hpart' :
        (∑ z ∈ LocalLemma.avoid E S, P₀.w z * W z) ≤
          M * LocalLemma.mass P₀.w (LocalLemma.avoid E S) := by
      rw [mass_pr]
      convert hpart using 1
      simp only [FinProb.expect, mul_ite, mul_zero]
      exact (Finset.sum_ite_mem_eq _ _).symm
    have hposS : 0 < LocalLemma.mass P₀.w (LocalLemma.avoid E S) := by
      have hmono : LocalLemma.avoid E Finset.univ ⊆ LocalLemma.avoid E S := by
        intro z hz
        simp only [LocalLemma.avoid, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact fun i hi => hz i trivial
      exact hmain.1.trans_le (Finset.sum_le_sum_of_subset_of_nonneg hmono
        (fun z _ _ => P₀.nonneg z))
    have hquot : (∑ z ∈ LocalLemma.avoid E S, P₀.w z * W z) /
        LocalLemma.mass P₀.w (LocalLemma.avoid E S) ≤ M := (div_le_iff₀ hposS).2 hpart'
    have hM : 0 ≤ M := by
      exact (Finset.sum_nonneg (fun z _ =>
        mul_nonneg ((resample P Λ z₀).nonneg z) (hW z))).trans (hR z₀)
    have hcomp := hmain.2.2.1 S T hST W hW
    rw [hUnion] at hcomp
    change (P₀.cond _ hpos).expect W ≤ _
    rw [cond_expect]
    exact hcomp.trans ((mul_le_mul_of_nonneg_left hquot
      (inv_nonneg.mpr (Finset.prod_nonneg fun i hi => sub_nonneg.mpr (hx1 i).le))).trans
        (mul_le_mul_of_nonneg_right (hcost Λ) hM))

theorem one_sub_sum_le_prod (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (S : Finset I) : 1 - ∑ i ∈ S, x i ≤ ∏ i ∈ S, (1 - x i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have hh := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hx1 i))
      have hs : 0 ≤ ∑ j ∈ S, x j := Finset.sum_nonneg fun j hj => hx0 j
      nlinarith [mul_nonneg (hx0 i) hs]

private theorem prod_union_lower (f : I → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1)
    (S T : Finset I) : (∏ i ∈ S, f i) * (∏ i ∈ T, f i) ≤ ∏ i ∈ S ∪ T, f i := by
  rw [← Finset.prod_union_inter]
  exact mul_le_of_le_one_right (Finset.prod_nonneg fun i hi => hf0 i)
    (Finset.prod_le_one₀ (fun i hi => hf0 i) (fun i hi => hf1 i))

/-- Total charge at most one half at each variable pays at most two per resampled variable. -/
theorem touching_charge_cost (scope : I → Finset V) (x : I → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hcharge : ∀ v, ∑ i ∈ Finset.univ.filter (fun i => v ∈ scope i), x i ≤ 1 / 2)
    (Λ : Finset V) :
    (∏ i ∈ Finset.univ.filter (fun i => ¬ Disjoint (scope i) Λ), (1 - x i))⁻¹ ≤ (2 : ℝ) ^ Λ.card := by
  let touch := fun Λ : Finset V => Finset.univ.filter fun i => ¬ Disjoint (scope i) Λ
  have hf0 (i) : 0 ≤ 1 - x i := sub_nonneg.mpr (hx1 i).le
  have hf1 (i) : 1 - x i ≤ 1 := by linarith [hx0 i]
  have hprod : ∀ Λ : Finset V, (1 / 2 : ℝ) ^ Λ.card ≤ ∏ i ∈ touch Λ, (1 - x i) := by
    intro Λ
    induction Λ using Finset.induction_on with
    | empty => simp [touch]
    | @insert v Λ hv ih =>
        let S := Finset.univ.filter fun i => v ∈ scope i
        have ht : touch (insert v Λ) = S ∪ touch Λ := by
          ext i
          simp only [touch, S, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_union, Finset.disjoint_insert_right]
          tauto
        have hs : (1 / 2 : ℝ) ≤ ∏ i ∈ S, (1 - x i) := by
          have hh := one_sub_sum_le_prod x hx0 (fun i => (hx1 i).le) S
          have hc := hcharge v
          change (∑ i ∈ S, x i) ≤ 1 / 2 at hc
          linarith
        rw [Finset.card_insert_of_notMem hv, pow_succ, ht]
        rw [mul_comm ((1 / 2 : ℝ) ^ Λ.card)]
        calc
          _ ≤ (∏ i ∈ S, (1 - x i)) * ∏ i ∈ touch Λ, (1 - x i) := by
            exact mul_le_mul hs ih (by positivity) (Finset.prod_nonneg fun i hi => hf0 i)
          _ ≤ _ := prod_union_lower _ hf0 hf1 S (touch Λ)
  have hh := hprod Λ
  have hp : 0 < (1 / 2 : ℝ) ^ Λ.card := by positivity
  have hi := (inv_le_inv₀ (hp.trans_le hh) hp).2 hh
  simpa only [touch, inv_pow, inv_div, one_div, inv_inv, inv_one, mul_one] using hi

theorem scoped_avoidance_of_charges (P : V → FinProb A) (Bad : I → (V → A) → Prop)
    (scope : I → Finset V) (hscope : ∀ i, FinProb.DependsOn (Bad i) (scope i))
    (x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hbad : ∀ i, (FinProb.pi P).pr (Bad i) ≤ x i / 2)
    (hneighbor : ∀ i, ∑ j ∈ Finset.univ.filter
      (fun j => i ≠ j ∧ ¬ Disjoint (scope i) (scope j)), x j ≤ 1 / 2)
    (hvariable : ∀ v, ∑ i ∈ Finset.univ.filter (fun i => v ∈ scope i), x i ≤ 1 / 2)
    (z₀ : V → A) :
    ∃ Q : FinProb (V → A),
      (∀ z, Q.w z ≠ 0 → (FinProb.pi P).w z ≠ 0 ∧ ∀ i, ¬ Bad i z) ∧
      ∀ (Λ : Finset V) (W : (V → A) → ℝ) (M : ℝ), (∀ z, 0 ≤ W z) →
        (∀ z, (resample P Λ z).expect W ≤ M) → Q.expect W ≤ (2 : ℝ) ^ Λ.card * M := by
  apply scoped_avoidance P Bad scope hscope x hx0 hx1 _
    (touching_charge_cost scope x hx0 hx1 hvariable) z₀
  intro i
  have hp := one_sub_sum_le_prod x hx0 (fun j => (hx1 j).le)
    (Finset.univ.filter (fun j => i ≠ j ∧ ¬ Disjoint (scope i) (scope j)))
  have hh := hneighbor i
  have hhalf : (1 / 2 : ℝ) ≤ ∏ j ∈ Finset.univ.filter
      (fun j => i ≠ j ∧ ¬ Disjoint (scope i) (scope j)), (1 - x j) := by linarith
  exact (hbad i).trans (by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hhalf (hx0 i))

end
end HypercubeRamsey.Lane_sol_s05_h5l
