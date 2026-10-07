import HypercubeRamsey.S05.History_sol_s05_hist1c
import HypercubeRamsey.S05.Bounds_sol_s05_h1

namespace HypercubeRamsey.Lane_sol_s05_hist1b

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-- Bayes comparison after deleting selected independent evidence coordinates.
Additional evidence `d` includes the partner labels at boundary keys. -/
theorem finite_bayes_delete_pi {Ω Δ ι : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Δ] [Fintype ι] [DecidableEq ι]
    {Ξ : ι → Type*} [∀ i, Fintype (Ξ i)]
    (P : FinProb Ω) (K : Ω → FinProb Δ) (J : ∀ ω : Ω, Δ → ∀ i, FinProb (Ξ i))
    (Q : ∀ i, FinProb (Ξ i)) (S : Finset ι) (ω₀ : Ω) (A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 < C)
    (hbound : ∀ ω d (z : ∀ i, Ξ i), (∏ i ∈ S, (J ω d i).w (z i)) ≤ A * ∏ i ∈ S, (Q i).w (z i)) :
    (FinProb.bind P fun ω => FinProb.bind (K ω) fun d => FinProb.pi (J ω d)).pr
      (fun x => ∃ ω,
        C * (normalize5 (fun u => P.w u * (K u).w x.2.1 *
          ∏ i ∈ Finset.univ \ S, (J u x.2.1 i).w (x.2.2 i)) ω₀).w ω <
          (normalize5 (fun u => P.w u * (K u).w x.2.1 *
            ∏ i, (J u x.2.1 i).w (x.2.2 i)) ω₀).w ω) ≤ A / C := by
  let D (d : Δ) (z : ∀ i, Ξ i) (ω : Ω) := P.w ω * (K ω).w d *
    ∏ i ∈ Finset.univ \ S, (J ω d i).w (z i)
  let L (d : Δ) (z : ∀ i, Ξ i) (ω : Ω) := ∏ i ∈ S, (J ω d i).w (z i)
  let F (d : Δ) (z : ∀ i, Ξ i) (ω : Ω) := D d z ω * L d z ω
  let md d z := ∑ ω, D d z ω
  let mf d z := ∑ ω, F d z ω
  let qr (z : ∀ i, Ξ i) := ∏ i ∈ S, (Q i).w (z i)
  let bad d z : Prop := ∃ ω,
    C * (normalize5 (D d z) ω₀).w ω < (normalize5 (F d z) ω₀).w ω
  have hD d z ω : 0 ≤ D d z ω := by
    exact mul_nonneg (mul_nonneg (P.nonneg ω) ((K ω).nonneg d))
      (Finset.prod_nonneg fun i _ => (J ω d i).nonneg _)
  have hL d z ω : 0 ≤ L d z ω := by
    exact Finset.prod_nonneg fun i _ => (J ω d i).nonneg _
  have hF d z ω : 0 ≤ F d z ω := mul_nonneg (hD d z ω) (hL d z ω)
  have hmd d z : 0 ≤ md d z := Finset.sum_nonneg fun ω _ => hD d z ω
  have hmf d z : 0 ≤ mf d z := Finset.sum_nonneg fun ω _ => hF d z ω
  have hqr z : 0 ≤ qr z := by
    exact Finset.prod_nonneg fun i _ => (Q i).nonneg _
  have hfactor d z ω : F d z ω = P.w ω * (K ω).w d * ∏ i, (J ω d i).w (z i) := by
    dsimp [F, D, L]
    rw [mul_assoc, ← Finset.prod_union Finset.sdiff_disjoint,
      Finset.sdiff_union_of_subset (Finset.subset_univ S)]
  have hFfun d z : F d z = (fun ω => P.w ω * (K ω).w d * ∏ i, (J ω d i).w (z i)) :=
    funext (hfactor d z)
  have hp d z : (if bad d z then mf d z else 0) ≤ A / C * md d z * qr z := by
    by_cases hb : bad d z
    · rw [if_pos hb]
      by_cases hz : mf d z = 0
      · rw [hz]; exact mul_nonneg (mul_nonneg (div_nonneg hA hC.le) (hmd d z)) (hqr z)
      have hfpos : 0 < mf d z := lt_of_le_of_ne (hmf d z) (Ne.symm hz)
      have hdpos : 0 < md d z := by
        by_contra hn
        have hd0 : md d z = 0 := le_antisymm (le_of_not_gt hn) (hmd d z)
        have hdω ω : D d z ω = 0 := by
          have hh := Finset.single_le_sum (fun u _ => hD d z u) (Finset.mem_univ ω)
          change D d z ω ≤ md d z at hh
          rw [hd0] at hh
          exact le_antisymm hh (hD d z ω)
        have : mf d z = 0 := by simp [mf, F, hdω]
        exact hz this
      obtain ⟨ω, hω⟩ := hb
      rw [Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg (D d z) ω₀ ω (hD d z) hdpos,
        Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg (F d z) ω₀ ω (hF d z) hfpos] at hω
      have hwpos : 0 < D d z ω := by
        by_contra hn
        have hw0 := le_antisymm (le_of_not_gt hn) (hD d z ω)
        simp [F, hw0] at hω
      have hcross := (div_lt_div_iff₀ hdpos hfpos).mp
        (show C * D d z ω / md d z < F d z ω / mf d z by simpa [mul_div_assoc] using hω)
      have hineq : C * mf d z < L d z ω * md d z := by
        apply (mul_lt_mul_iff_right₀ hwpos).mp
        calc
          D d z ω * (C * mf d z) = C * D d z ω * mf d z := by ring
          _ < F d z ω * md d z := hcross
          _ = D d z ω * (L d z ω * md d z) := by dsimp [F]; ring
      have hbnd := mul_le_mul_of_nonneg_right (hbound ω d z) (hmd d z)
      change L d z ω * md d z ≤ A * qr z * md d z at hbnd
      have hh := (le_div_iff₀ hC).mpr
        (show mf d z * C ≤ A * qr z * md d z by nlinarith [hineq.le.trans hbnd])
      exact hh.trans_eq (by ring)
    · rw [if_neg hb]; exact mul_nonneg (mul_nonneg (div_nonneg hA hC.le) (hmd d z)) (hqr z)
  have ht : ∑ d, ∑ z, md d z * qr z = 1 := by
    simp only [md, D, Finset.sum_mul]
    simp_rw [Finset.sum_comm (f := fun z ω =>
      P.w ω * (K ω).w _ * (∏ i ∈ Finset.univ \ S, (J ω _ i).w (z i)) * qr z)]
    rw [Finset.sum_comm]
    apply Eq.trans _ P.sum_eq_one
    apply Finset.sum_congr rfl
    intro ω _
    calc
      _ = P.w ω * ∑ d, (K ω).w d * ∑ z : ∀ i, Ξ i, ∏ i, (if i ∈ S then Q i else J ω d i).w (z i) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro z _
        have hprod : (∏ i ∈ Finset.univ \ S, (J ω d i).w (z i)) * qr z =
            ∏ i, (if i ∈ S then Q i else J ω d i).w (z i) := by
          change _ * (∏ i ∈ S, (Q i).w (z i)) = _
          let f i := (if i ∈ S then Q i else J ω d i).w (z i)
          have h1 : (∏ i ∈ Finset.univ \ S, (J ω d i).w (z i)) = ∏ i ∈ Finset.univ \ S, f i := by
            apply Finset.prod_congr rfl
            intro i hi
            simp [f, (Finset.mem_sdiff.mp hi).2]
          have h2 : (∏ i ∈ S, (Q i).w (z i)) = ∏ i ∈ S, f i := by
            apply Finset.prod_congr rfl
            intro i hi
            simp [f, hi]
          rw [h1, h2, ← Finset.prod_union Finset.sdiff_disjoint,
            Finset.sdiff_union_of_subset (Finset.subset_univ S)]
        rw [mul_assoc, mul_assoc, hprod]
      _ = P.w ω := by
        simp_rw [show ∀ d, (∑ z : ∀ i, Ξ i, ∏ i, (if i ∈ S then Q i else J ω d i).w (z i)) = 1 from
          fun d => (FinProb.pi fun i => if i ∈ S then Q i else J ω d i).sum_eq_one]
        simp [(K ω).sum_eq_one]
  have heq : (FinProb.bind P fun ω => FinProb.bind (K ω) fun d => FinProb.pi (J ω d)).pr
      (fun x => ∃ ω,
        C * (normalize5 (fun u => P.w u * (K u).w x.2.1 *
          ∏ i ∈ Finset.univ \ S, (J u x.2.1 i).w (x.2.2 i)) ω₀).w ω <
          (normalize5 (fun u => P.w u * (K u).w x.2.1 *
            ∏ i, (J u x.2.1 i).w (x.2.2 i)) ω₀).w ω) =
      ∑ d, ∑ z, if bad d z then mf d z else 0 := by
    unfold FinProb.pr
    simp only [FinProb.bind, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    have hbad : bad d z ↔ ∃ ω,
        C * (normalize5 (fun u => P.w u * (K u).w d *
          ∏ i ∈ Finset.univ \ S, (J u d i).w (z i)) ω₀).w ω <
          (normalize5 (fun u => P.w u * (K u).w d * ∏ i, (J u d i).w (z i)) ω₀).w ω := by
      simp only [bad, D, hFfun]
    simp only [← hbad]
    by_cases hb : bad d z <;> simp [hb, mf, hfactor, FinProb.pi, mul_assoc]
  rw [heq]
  calc
    _ ≤ ∑ d, ∑ z, A / C * md d z * qr z :=
      Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun z _ => hp d z
    _ = A / C := by
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [ht, mul_one]

/-- A product law restricted along an injection is the product of its selected laws. -/
theorem pi_injection_expect {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype Ω]
    (P : ι → FinProb Ω) (e : κ → ι) (he : Function.Injective e) (f : (κ → Ω) → ℝ) :
    (FinProb.pi P).expect (fun u => f (fun i => u (e i))) =
      (FinProb.pi fun i => P (e i)).expect f := by
  let S := Finset.univ.image e
  let es : κ ≃ S := Equiv.ofBijective (fun i => ⟨e i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun i j h => he (congrArg Subtype.val h), by
      intro i
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.2
      exact ⟨j, Subtype.ext hj⟩⟩
  let ef : (κ → Ω) ≃ (S → Ω) := {
    toFun := fun u i => u (es.symm i)
    invFun := fun u i => u (es i)
    left_inv := by intro u; funext i; simp
    right_inv := by intro u; funext i; simp }
  have hm := FinProb.pi_marginal_expect P S (fun u => f (fun i => u (es i)))
  change (FinProb.pi P).expect (fun u => f (fun i => u (e i))) = _ at hm
  rw [hm]
  unfold FinProb.expect
  rw [← Equiv.sum_comp ef]
  apply Finset.sum_congr rfl
  intro u _
  have hp : (FinProb.pi fun i : S => P i.1).w (ef u) =
      (FinProb.pi fun i => P (e i)).w u := by
    unfold FinProb.pi
    exact (Fintype.prod_equiv es _ _ (fun i => by simp only [ef, Equiv.coe_fn_mk, Equiv.symm_apply_apply]; rfl)).symm
  rw [hp]
  congr 1
  change f (fun i => (ef u) (es i)) = f u
  congr 1
  funext i
  simp [ef]

/-- Flatten the two independent coordinate indices of a stream product. -/
theorem pi_flatten_expect {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype Ω]
    (P : ι → κ → FinProb Ω) (f : ((ι × κ) → Ω) → ℝ) :
    (FinProb.pi fun i => FinProb.pi (P i)).expect (fun u => f (fun c => u c.1 c.2)) =
      (FinProb.pi fun c : ι × κ => P c.1 c.2).expect f := by
  let e : ((ι × κ) → Ω) ≃ (ι → κ → Ω) := {
    toFun := fun u i j => u (i, j)
    invFun := fun u c => u c.1 c.2
    left_inv := by intro u; rfl
    right_inv := by intro u; rfl }
  unfold FinProb.expect
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro u _
  change (∏ i, ∏ j, (P i j).w (u (i, j))) * f (fun c => u (c.1, c.2)) =
    (∏ c : ι × κ, (P c.1 c.2).w (u c)) * f u
  rw [Fintype.prod_prod_type]

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

/-- Integrate all bins and segments absent from the specified boundary observation. -/
theorem coarse_prefix_expect (v : Fin N) (B : Finset (BinVector5 n))
    (k : ℕ) (hk : k ≤ X.p.streamSegs n)
    (f : (B → Fin N) → ((B × Fin k) → Word5 N X.p.q0) → ℝ) :
    (X.coarseLaw v).expect (fun c => f (fun w => c.1 w.1)
      (fun ws => c.2 ws.1.1 (Fin.castLE hk ws.2))) =
      (FinProb.bind (FinProb.pi fun w : B => X.P.prior.partner v w.1)
        (fun A => FinProb.pi fun ws : B × Fin k => X.segLaw v (A ws.1))).expect
          (fun az => f az.1 az.2) := by
  rw [Setup5.coarseLaw]
  rw [FinProb.bind_expect (FinProb.pi fun w => X.P.prior.partner v w)
    (fun A => FinProb.pi fun w => FinProb.pi fun _ : Fin (X.p.streamSegs n) => X.segLaw v (A w))
    (fun A W => f (fun w : B => A w.1) (fun ws : B × Fin k => W ws.1.1 (Fin.castLE hk ws.2)))]
  rw [FinProb.bind_expect]
  have hs (A : BinVector5 n → Fin N) :
      (FinProb.pi fun w => FinProb.pi fun _ : Fin (X.p.streamSegs n) => X.segLaw v (A w)).expect
        (fun W => f (fun w : B => A w.1) (fun ws : B × Fin k => W ws.1.1 (Fin.castLE hk ws.2))) =
      (FinProb.pi fun ws : B × Fin k => X.segLaw v (A ws.1.1)).expect (f (fun w : B => A w.1)) := by
    rw [pi_flatten_expect (fun w (_ : Fin (X.p.streamSegs n)) => X.segLaw v (A w))
      (fun Z => f (fun w : B => A w.1) (fun ws : B × Fin k => Z (ws.1.1, Fin.castLE hk ws.2)))]
    exact pi_injection_expect (fun ws : BinVector5 n × Fin (X.p.streamSegs n) => X.segLaw v (A ws.1))
      (fun ws : B × Fin k => (ws.1.1, Fin.castLE hk ws.2))
      (by intro a b h; apply Prod.ext; exact Subtype.ext (congrArg (fun c => c.1) h)
          exact Fin.ext (congrArg (fun c => c.2.val) h)) _
  simp_rw [hs]
  simpa only [FinProb.expect] using
    pi_injection_expect (fun w => X.P.prior.partner v w) Subtype.val Subtype.val_injective
      (fun A : B → Fin N => (FinProb.pi fun ws : B × Fin k => X.segLaw v (A ws.1)).expect (f A))

private theorem prefix_prod {k t : ℕ} (h : k ≤ t) (f : Fin t → ℝ) :
    (∏ s : Fin t, if (s : ℕ) < k then f s else 1) = ∏ s : Fin k, f (Fin.castLE h s) := by
  let S : Finset (Fin t) := Finset.univ.filter fun s => (s : ℕ) < k
  let e : Fin k ≃ S := {
    toFun := fun s => ⟨Fin.castLE h s, by simp [S, s.isLt]⟩
    invFun := fun s => ⟨s.1.val, (Finset.mem_filter.mp s.2).2⟩
    left_inv := by intro s; rfl
    right_inv := by intro s; rfl }
  calc
    _ = ∏ s ∈ S, f s := by simp [S, Finset.prod_filter]
    _ = ∏ s : S, f s.1 := by
      rw [Finset.univ_eq_attach]
      exact (Finset.prod_attach S f).symm
    _ = _ := (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm

/-- Every key's observed prefix is present in the raw stream. -/
theorem key_prefix_le_stream (ℓ : X.Key) : X.p.uSeg n (ℓ.level + 1) ≤ X.p.streamSegs n := by
  have hl : ℓ.level ≤ X.p.J n := by
    cases ℓ with
    | inl k => exact Nat.le_of_lt_succ k.2.2.isLt
    | inr i => exact le_refl _
  exact (Lane_q_s05_hist1b.uSeg_mono5 X.p n _ _ (Nat.add_le_add_right hl 1)).trans (Nat.le_max_left _ _)

/-- Boundary posterior weights are exactly the finite observed-evidence weights. -/
theorem colWeight_boundary_observed (b : X.Base) (ℓ : X.Key) (hb : ℓ.coarse.2 = true)
    (keep : BinVector5 n → Fin (X.p.streamSegs n) → Prop) (y : Fin N) :
    X.colWeight b ℓ b.2.2 keep y = X.P.prior.parent.w y *
      (∏ w : binList5 ℓ.coarse, (X.P.prior.partner y w.1).w (b.2.1 w.1)) *
      ∏ ws : (binList5 ℓ.coarse) × Fin (X.p.uSeg n (ℓ.level + 1)),
        if keep ws.1.1 (Fin.castLE (key_prefix_le_stream X ℓ) ws.2)
        then (X.segLaw y (b.2.1 ws.1.1)).w
          (b.2.2 ws.1.1 (Fin.castLE (key_prefix_le_stream X ℓ) ws.2)) else 1 := by
  classical
  unfold Setup5.colWeight
  simp only [hb, ite_true]
  have hp (w : BinVector5 n) :
      (∏ s : Fin (X.p.streamSegs n),
        if (s : ℕ) < X.p.uSeg n (ℓ.level + 1) ∧ keep w s
        then (X.segLaw y (b.2.1 w)).w (b.2.2 w s) else 1) =
      ∏ s : Fin (X.p.uSeg n (ℓ.level + 1)),
        if keep w (Fin.castLE (key_prefix_le_stream X ℓ) s)
        then (X.segLaw y (b.2.1 w)).w (b.2.2 w (Fin.castLE (key_prefix_le_stream X ℓ) s)) else 1 := by
    simpa only [ite_and] using prefix_prod (key_prefix_le_stream X ℓ)
      (fun s => if keep w s then (X.segLaw y (b.2.1 w)).w (b.2.2 w s) else 1)
  simp_rw [hp]
  rw [← Finset.prod_attach (binList5 ℓ.coarse)]
  rw [← Finset.univ_eq_attach, Finset.prod_mul_distrib, Fintype.prod_prod_type]
  ring

/-- The selected-bin stream likelihood has the required density at the deletion scale. -/
theorem selected_prefix_density (B : Finset (BinVector5 n)) (l k : ℕ)
    (w : BinVector5 n) (v : Fin N) (A : B → Fin N)
    (z : (B × Fin l) → Word5 N X.p.q0) :
    (∏ ws ∈ Finset.univ.filter (fun ws : B × Fin l => ws.1.1 = w ∧ (ws.2 : ℕ) < k),
      (X.segLaw v (A ws.1)).w (z ws)) ≤ Real.exp (X.p.a 0 * (X.p.q0 * k)) *
      ∏ ws ∈ Finset.univ.filter (fun ws : B × Fin l => ws.1.1 = w ∧ (ws.2 : ℕ) < k),
        X.S.reference.w (z ws) := by
  classical
  let S := Finset.univ.filter (fun ws : B × Fin l => ws.1.1 = w ∧ (ws.2 : ℕ) < k)
  have hcard : S.card ≤ k := by
    let f : S → Fin k := fun ws => ⟨ws.1.2.val, (Finset.mem_filter.mp ws.2).2.2⟩
    have hinj : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact (Finset.mem_filter.mp a.2).2.1.trans (Finset.mem_filter.mp b.2).2.1.symm
      · have hv := congrArg Fin.val h
        change a.1.2.val = b.1.2.val at hv
        exact Fin.ext hv
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hinj
  have hnonneg : 0 ≤ X.p.a 0 * X.p.q0 := by rw [X.p.ha0]; positivity
  have hrate : Real.exp (X.p.a 0 * X.p.q0) ^ S.card ≤ Real.exp (X.p.a 0 * (X.p.q0 * k)) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right (show (S.card : ℝ) ≤ k by exact_mod_cast hcard) hnonneg
    push_cast
    nlinarith
  calc
    _ ≤ ∏ ws ∈ S, Real.exp (X.p.a 0 * X.p.q0) * X.S.reference.w (z ws) :=
      Finset.prod_le_prod₀ (fun ws _ => (X.segLaw v (A ws.1)).nonneg _)
        (fun ws _ => segLaw_density X _ _ _)
    _ = Real.exp (X.p.a 0 * X.p.q0) ^ S.card * ∏ ws ∈ S, X.S.reference.w (z ws) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ _ := mul_le_mul_of_nonneg_right hrate (Finset.prod_nonneg fun _ _ => X.S.reference.nonneg _)

private def indic (A : Prop) : ℝ := if A then 1 else 0

private theorem pr_indic {α : Type*} [Fintype α] (P : FinProb α) (f : α → Prop) :
    P.pr f = P.expect (fun x => indic (f x)) := by
  unfold FinProb.pr FinProb.expect indic
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x <;> simp only [h, ite_true, ite_false, mul_one, mul_zero]

private theorem pr_bind_indic {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (f : α × β → Prop) :
    (FinProb.bind P K).pr f = ∑ a, P.w a * (K a).expect (fun b => indic (f (a, b))) := by
  unfold FinProb.pr FinProb.expect indic
  simp only [FinProb.bind, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : f (a, b) <;> simp only [h, ite_true, ite_false, mul_one, mul_zero]

/-- The raw Step 1 comparison at a boundary key, with every unused bin and
segment integrated out. -/
theorem boundary_step1_raw_bound (ℓ : X.Key) (hb : ℓ.coarse.2 = true)
    (w : BinVector5 n) (k : ℕ) :
    X.baseLaw.pr (fun b => X.step1Fail b ℓ w k) ≤ Real.exp (-(X.p.delta * (X.p.q0 * k))) := by
  classical
  let B := binList5 ℓ.coarse
  let l := X.p.uSeg n (ℓ.level + 1)
  let S := Finset.univ.filter (fun ws : B × Fin l => ws.1.1 = w ∧ (ws.2 : ℕ) < k)
  let K (v : Fin N) := FinProb.pi fun w : B => X.P.prior.partner v w.1
  let J (v : Fin N) (A : B → Fin N) (ws : B × Fin l) := X.segLaw v (A ws.1)
  let Q (_ : B × Fin l) := X.S.reference
  let A := Real.exp (X.p.a 0 * (X.p.q0 * k))
  let C := Real.exp (X.p.a 1 * (X.p.q0 * k))
  let bad (a : B → Fin N) (z : (B × Fin l) → Word5 N X.p.q0) : Prop := ∃ y,
    C * (normalize5 (fun v => X.P.prior.parent.w v * (K v).w a *
      ∏ ws ∈ Finset.univ \ S, (J v a ws).w (z ws)) X.y₀).w y <
      (normalize5 (fun v => X.P.prior.parent.w v * (K v).w a *
        ∏ ws, (J v a ws).w (z ws)) X.y₀).w y
  have hset : Finset.univ \ S = Finset.univ.filter
      (fun ws : B × Fin l => ¬ (ws.1.1 = w ∧ (ws.2 : ℕ) < k)) := by
    ext ws
    simp [S]
  have hbad (b : X.Base) : X.step1Fail b ℓ w k ↔
      bad (fun w : B => b.2.1 w.1)
        (fun ws : B × Fin l => b.2.2 ws.1.1 (Fin.castLE (key_prefix_le_stream X ℓ) ws.2)) := by
    unfold Setup5.step1Fail Setup5.prior Setup5.priorDel
    have hh (keep : BinVector5 n → Fin (X.p.streamSegs n) → Prop) :=
      funext (colWeight_boundary_observed X b ℓ hb keep)
    rw [hh (fun w' s => ¬ (w' = w ∧ (s : ℕ) < k)), hh (fun _ _ => True)]
    dsimp [bad, C, K, J, FinProb.pi]
    rw [hset]
    simp only [Finset.prod_filter, Fin.castLE, ite_true]
    rfl
  have hraw : X.baseLaw.pr (fun b => X.step1Fail b ℓ w k) =
      (FinProb.bind X.P.prior.parent fun v => FinProb.bind (K v) fun a => FinProb.pi (J v a)).pr
        (fun x => bad x.2.1 x.2.2) := by
    simp_rw [hbad]
    rw [Setup5.baseLaw, pr_bind_indic]
    have hobs (v : Fin N) := coarse_prefix_expect X v B l (key_prefix_le_stream X ℓ)
      (fun a z => indic (bad a z))
    simp_rw [hobs]
    rw [pr_bind_indic]
  have hfinite := finite_bayes_delete_pi X.P.prior.parent K J Q S X.y₀ A C
    (Real.exp_pos _).le (Real.exp_pos _)
    (fun v a z => selected_prefix_density X B l k w v a z)
  change (FinProb.bind X.P.prior.parent fun v => FinProb.bind (K v) fun a => FinProb.pi (J v a)).pr
    (fun x => bad x.2.1 x.2.2) ≤ A / C at hfinite
  rw [hraw]
  apply hfinite.trans
  dsimp [A, C]
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hgap := X.p.hdelta_a (0 : Fin 9) 1 (by decide)
  have hd := X.p.hdelta.1
  have hslack : X.p.delta ≤ X.p.a 1 - X.p.a 0 := by linarith
  have hm := mul_le_mul_of_nonneg_right hslack (Nat.cast_nonneg (X.p.q0 * k))
  push_cast at hm
  nlinarith

private theorem pi_eval_expect {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (P : ι → FinProb Ω) (i : ι) (f : Ω → ℝ) :
    (FinProb.pi P).expect (fun u => f (u i)) = (P i).expect f := by
  have h := pi_injection_expect P (fun _ : Unit => i)
    (fun _ _ _ => Subsingleton.elim _ _) (fun u => f (u ()))
  change (FinProb.pi P).expect (fun u => f (u i)) = _ at h
  rw [h]
  unfold FinProb.expect
  rw [← Equiv.sum_comp (Equiv.funUnique Unit Ω).symm]
  apply Finset.sum_congr rfl
  intro x _
  simp [FinProb.pi, Equiv.funUnique, Equiv.piUnique]

/-- The raw marginal at an interior key reads one partner and its prefix. -/
theorem coarse_single_prefix_expect (v : Fin N) (w : BinVector5 n) (k : ℕ)
    (hk : k ≤ X.p.streamSegs n) (f : (Fin k → Word5 N X.p.q0) → ℝ) :
    (X.coarseLaw v).expect (fun c => f (fun s => c.2 w (Fin.castLE hk s))) =
      (FinProb.bind (X.P.prior.partner v w)
        (fun a => FinProb.pi fun _ : Fin k => X.segLaw v a)).expect (fun az => f az.2) := by
  rw [Setup5.coarseLaw]
  rw [FinProb.bind_expect (FinProb.pi fun w => X.P.prior.partner v w)
    (fun A => FinProb.pi fun w => FinProb.pi fun _ : Fin (X.p.streamSegs n) => X.segLaw v (A w))
    (fun A W => f (fun s => W w (Fin.castLE hk s)))]
  rw [FinProb.bind_expect (X.P.prior.partner v w)
    (fun a => FinProb.pi fun _ : Fin k => X.segLaw v a) (fun _ z => f z)]
  have hs (A : BinVector5 n → Fin N) :
      (FinProb.pi fun w => FinProb.pi fun _ : Fin (X.p.streamSegs n) => X.segLaw v (A w)).expect
        (fun W => f (fun s => W w (Fin.castLE hk s))) =
      (FinProb.pi fun _ : Fin k => X.segLaw v (A w)).expect f := by
    rw [pi_flatten_expect (fun w (_ : Fin (X.p.streamSegs n)) => X.segLaw v (A w))
      (fun Z => f (fun s => Z (w, Fin.castLE hk s)))]
    exact pi_injection_expect (fun ws : BinVector5 n × Fin (X.p.streamSegs n) => X.segLaw v (A ws.1))
      (fun s : Fin k => (w, Fin.castLE hk s))
      (by intro a b h; exact Fin.ext (congrArg (fun c => c.2.val) h)) f
  simp_rw [hs]
  simpa only [FinProb.expect] using pi_eval_expect (fun w => X.P.prior.partner v w) w
    (fun a => (FinProb.pi fun _ : Fin k => X.segLaw v a).expect f)

/-- Interior posterior weights are exactly the observed prefix weights. -/
theorem colWeight_interior_observed (b : X.Base) (ℓ : X.Key) (hb : ℓ.coarse.2 = false)
    (keep : BinVector5 n → Fin (X.p.streamSegs n) → Prop) (y : Fin N) :
    X.colWeight b ℓ b.2.2 keep y = (X.P.prior.partner b.1 ℓ.coarse.1).w y *
      ∏ s : Fin (X.p.uSeg n (ℓ.level + 1)),
        if keep ℓ.coarse.1 (Fin.castLE (key_prefix_le_stream X ℓ) s)
        then (X.segLaw b.1 y).w (b.2.2 ℓ.coarse.1 (Fin.castLE (key_prefix_le_stream X ℓ) s)) else 1 := by
  unfold Setup5.colWeight
  simp only [hb, Bool.false_eq_true, ite_false]
  congr 1
  simpa only [ite_and] using prefix_prod (key_prefix_le_stream X ℓ)
    (fun s => if keep ℓ.coarse.1 s then (X.segLaw b.1 y).w (b.2.2 ℓ.coarse.1 s) else 1)

/-- The finite interior comparison law, with any deleted prefix length. -/
theorem interior_prefix_comparison (v : Fin N) (w : BinVector5 n) (l k : ℕ) :
    (FinProb.bind (X.P.prior.partner v w)
      (fun a => FinProb.pi fun _ : Fin l => X.segLaw v a)).pr (fun az => ∃ y,
      Real.exp (X.p.a 1 * (X.p.q0 * k)) *
        (normalize5 (fun a => (X.P.prior.partner v w).w a *
          ∏ s : Fin l, if ¬ ((s : ℕ) < k) then (X.segLaw v a).w (az.2 s) else 1) X.y₀).w y <
        (normalize5 (fun a => (X.P.prior.partner v w).w a *
          ∏ s : Fin l, (X.segLaw v a).w (az.2 s)) X.y₀).w y) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * k))) := by
  classical
  let U : FinProb Unit := FinProb.uniform Finset.univ ⟨(), Finset.mem_univ _⟩
  let S : Finset (Fin l) := Finset.univ.filter fun s => (s : ℕ) < k
  let A := Real.exp (X.p.a 0 * (X.p.q0 * k))
  let C := Real.exp (X.p.a 1 * (X.p.q0 * k))
  have hbound (a : Fin N) (_ : Unit) (z : Fin l → Word5 N X.p.q0) :
      (∏ s ∈ S, (X.segLaw v a).w (z s)) ≤ A * ∏ s ∈ S, X.S.reference.w (z s) := by
    have hc : S.card ≤ k := by
      let e : S → Fin k := fun s => ⟨s.1.val, (Finset.mem_filter.mp s.2).2⟩
      simpa only [Fintype.card_coe, Fintype.card_fin] using
        Fintype.card_le_of_injective e (by
          intro a b h
          have hv := congrArg Fin.val h
          change a.1.val = b.1.val at hv
          exact Subtype.ext (Fin.ext hv))
    have hrate : Real.exp (X.p.a 0 * X.p.q0) ^ S.card ≤ A := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hp : 0 ≤ X.p.a 0 * X.p.q0 := by rw [X.p.ha0]; positivity
      have hh := mul_le_mul_of_nonneg_right (show (S.card : ℝ) ≤ k by exact_mod_cast hc) hp
      push_cast
      nlinarith
    calc
      _ ≤ ∏ s ∈ S, Real.exp (X.p.a 0 * X.p.q0) * X.S.reference.w (z s) :=
        Finset.prod_le_prod₀ (fun s _ => (X.segLaw v a).nonneg _)
          (fun s _ => segLaw_density X _ _ _)
      _ = Real.exp (X.p.a 0 * X.p.q0) ^ S.card * ∏ s ∈ S, X.S.reference.w (z s) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right hrate (Finset.prod_nonneg fun _ _ => X.S.reference.nonneg _)
  have hf := finite_bayes_delete_pi (X.P.prior.partner v w) (fun _ => U)
    (fun a (_ : Unit) (_ : Fin l) => X.segLaw v a) (fun _ : Fin l => X.S.reference)
    S X.y₀ A C (Real.exp_pos _).le (Real.exp_pos _) hbound
  have hset : Finset.univ \ S = Finset.univ.filter (fun s : Fin l => ¬ ((s : ℕ) < k)) := by
    ext s; simp [S]
  rw [hset] at hf
  simp only [Finset.prod_filter] at hf
  have hh : (FinProb.bind (X.P.prior.partner v w)
      (fun a => FinProb.pi fun _ : Fin l => X.segLaw v a)).pr (fun az => ∃ y,
      C * (normalize5 (fun a => (X.P.prior.partner v w).w a *
        ∏ s : Fin l, if ¬ ((s : ℕ) < k) then (X.segLaw v a).w (az.2 s) else 1) X.y₀).w y <
      (normalize5 (fun a => (X.P.prior.partner v w).w a *
        ∏ s : Fin l, (X.segLaw v a).w (az.2 s)) X.y₀).w y) ≤ A / C := by
    simpa [U, FinProb.uniform, FinProb.pr, FinProb.bind, Fintype.sum_prod_type] using hf
  apply hh.trans
  dsimp [A, C]
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hgap := X.p.hdelta_a (0 : Fin 9) 1 (by decide)
  have hd := X.p.hdelta.1
  have hslack : X.p.delta ≤ X.p.a 1 - X.p.a 0 := by linarith
  have hm := mul_le_mul_of_nonneg_right hslack (Nat.cast_nonneg (X.p.q0 * k))
  push_cast at hm
  nlinarith

/-- The raw Step 1 comparison at an interior key. -/
theorem interior_step1_raw_bound (ℓ : X.Key) (hb : ℓ.coarse.2 = false) (k : ℕ) :
    X.baseLaw.pr (fun b => X.step1Fail b ℓ ℓ.coarse.1 k) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * k))) := by
  classical
  let l := X.p.uSeg n (ℓ.level + 1)
  let w := ℓ.coarse.1
  let bad (v : Fin N) (z : Fin l → Word5 N X.p.q0) : Prop := ∃ y,
    Real.exp (X.p.a 1 * (X.p.q0 * k)) *
      (normalize5 (fun a => (X.P.prior.partner v w).w a *
        ∏ s : Fin l, if ¬ ((s : ℕ) < k) then (X.segLaw v a).w (z s) else 1) X.y₀).w y <
      (normalize5 (fun a => (X.P.prior.partner v w).w a *
        ∏ s : Fin l, (X.segLaw v a).w (z s)) X.y₀).w y
  let R (v : Fin N) := FinProb.bind (X.P.prior.partner v w)
    (fun a => FinProb.pi fun _ : Fin l => X.segLaw v a)
  have hbad (b : X.Base) : X.step1Fail b ℓ w k ↔
      bad b.1 (fun s => b.2.2 w (Fin.castLE (key_prefix_le_stream X ℓ) s)) := by
    unfold Setup5.step1Fail Setup5.prior Setup5.priorDel
    have hh (keep : BinVector5 n → Fin (X.p.streamSegs n) → Prop) :=
      funext (colWeight_interior_observed X b ℓ hb keep)
    rw [hh (fun w' s => ¬ (w' = w ∧ (s : ℕ) < k)), hh (fun _ _ => True)]
    simp only [w, not_true_eq_false, true_and, ite_true]
    rfl
  have heq : X.baseLaw.pr (fun b => X.step1Fail b ℓ w k) =
      ∑ v, X.P.prior.parent.w v * (R v).pr (fun az => bad v az.2) := by
    simp_rw [hbad]
    rw [Setup5.baseLaw, pr_bind_indic]
    have hobs (v : Fin N) := coarse_single_prefix_expect X v w l (key_prefix_le_stream X ℓ)
      (fun z => indic (bad v z))
    simp_rw [hobs]
    simp_rw [pr_indic]
    rfl
  rw [heq]
  calc
    _ ≤ ∑ v, X.P.prior.parent.w v * Real.exp (-(X.p.delta * (X.p.q0 * k))) := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_left (interior_prefix_comparison X v w l k) (X.P.prior.parent.nonneg v)
    _ = _ := by rw [← Finset.sum_mul, X.P.prior.parent.sum_eq_one, one_mul]

/-- All Step 1 comparisons hold with the raw exponential rate, without
an eventual dimension restriction. -/
theorem step1_comparison_raw_bound (ℓ : X.Key) (w : BinVector5 n) (k : ℕ) :
    X.baseLaw.pr (fun b => X.step1Fail b ℓ w k) ≤ Real.exp (-(X.p.delta * (X.p.q0 * k))) := by
  classical
  cases hb : ℓ.coarse.2 with
  | true => exact boundary_step1_raw_bound X ℓ hb w k
  | false =>
    by_cases hw : w = ℓ.coarse.1
    · subst w
      exact interior_step1_raw_bound X ℓ hb k
    have hdel (b : X.Base) : X.priorDel b ℓ w k = X.prior b ℓ := by
      unfold Setup5.priorDel Setup5.prior
      congr 1
      funext y
      simp [Setup5.colWeight, hb, Ne.symm hw]
    have hC : 1 ≤ Real.exp (X.p.a 1 * (X.p.q0 * k)) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have ha : 0 < X.p.a 1 := by
        have hh := X.p.ha_order (0 : Fin 9) 1 (by decide)
        rw [X.p.ha0] at hh
        linarith
      positivity
    have hn (b : X.Base) : ¬ X.step1Fail b ℓ w k := by
      rintro ⟨y, hy⟩
      rw [hdel] at hy
      have h := mul_le_mul_of_nonneg_right hC ((X.prior b ℓ).nonneg y)
      simp only [one_mul] at h
      exact not_lt_of_ge h hy
    simp [FinProb.pr, hn, (Real.exp_pos _).le]

/-- The same raw marginal in the nested representation used by the cap lemma. -/
theorem coarse_prefix_nested_expect (v : Fin N) (B : Finset (BinVector5 n))
    (k : ℕ) (hk : k ≤ X.p.streamSegs n)
    (f : (B → Fin N) → (B → Fin k → Word5 N X.p.q0) → ℝ) :
    (X.coarseLaw v).expect (fun c => f (fun w => c.1 w.1)
      (fun w s => c.2 w.1 (Fin.castLE hk s))) =
      (boundary_prefix_kernel X B k v).expect (fun az => f az.1 az.2) := by
  rw [coarse_prefix_expect X v B k hk (fun A z => f A (fun w s => z (w, s)))]
  rw [boundary_prefix_kernel]
  rw [FinProb.bind_expect (FinProb.pi fun w : B => X.P.prior.partner v w.1)
    (fun A => FinProb.pi fun w : B => FinProb.pi fun _ : Fin k => X.segLaw v (A w))
    (fun A z => f A z)]
  rw [FinProb.bind_expect (FinProb.pi fun w : B => X.P.prior.partner v w.1)
    (fun A => FinProb.pi fun ws : B × Fin k => X.segLaw v (A ws.1))
    (fun A z => f A (fun w s => z (w, s)))]
  apply Finset.sum_congr rfl
  intro A _
  congr 1
  exact (pi_flatten_expect (fun w (_ : Fin k) => X.segLaw v (A w))
    (fun z => f A (fun w s => z (w, s)))).symm

/-- The boundary prior cap in the actual raw Setup5 law. -/
theorem boundary_cap_raw_bound (ℓ : X.Key) (hb : ℓ.coarse.2 = true) :
    X.baseLaw.pr (fun b => X.capFail b ℓ) ≤
      ((4 / χ ^ 2) * (((4 / χ ^ 2) *
        Real.exp (X.p.a 0 * (X.p.q0 * X.p.uSeg n (ℓ.level + 1)))) ^ (binList5 ℓ.coarse).card)) /
        Real.exp (X.p.Kcap * (X.p.q0 * X.p.uSeg n (ℓ.level + 1))) := by
  classical
  let B := binList5 ℓ.coarse
  let l := X.p.uSeg n (ℓ.level + 1)
  let bad (A : B → Fin N) (z : B → Fin l → Word5 N X.p.q0) : Prop := ∃ y,
    Real.exp (X.p.Kcap * (X.p.q0 * l)) < (N : ℝ) *
      (normalize5 (fun v => X.P.prior.parent.w v * (boundary_prefix_kernel X B l v).w (A, z)) X.y₀).w y
  have hbad (b : X.Base) : X.capFail b ℓ ↔
      bad (fun w : B => b.2.1 w.1)
        (fun w s => b.2.2 w.1 (Fin.castLE (key_prefix_le_stream X ℓ) s)) := by
    unfold Setup5.capFail Setup5.prior
    have hh := funext (colWeight_boundary_observed X b ℓ hb (fun _ _ => True))
    rw [hh]
    dsimp [bad, boundary_prefix_kernel, FinProb.bind, FinProb.pi]
    simp only [ite_true, Fintype.prod_prod_type, mul_assoc]
    rfl
  have hraw : X.baseLaw.pr (fun b => X.capFail b ℓ) =
      (FinProb.bind X.P.prior.parent (boundary_prefix_kernel X B l)).pr
        (fun x => bad x.2.1 x.2.2) := by
    simp_rw [hbad]
    rw [Setup5.baseLaw, pr_bind_indic]
    have hobs (v : Fin N) := coarse_prefix_nested_expect X v B l (key_prefix_le_stream X ℓ)
      (fun A z => indic (bad A z))
    simp_rw [hobs]
    rw [pr_bind_indic]
  rw [hraw]
  exact boundary_prefix_cap X B l

/-- The interior prior cap in the actual raw Setup5 law. -/
theorem interior_cap_raw_bound (ℓ : X.Key) (hb : ℓ.coarse.2 = false) :
    X.baseLaw.pr (fun b => X.capFail b ℓ) ≤
      (4 / χ ^ 2) * Real.exp (X.p.a 0 * (X.p.q0 * X.p.uSeg n (ℓ.level + 1))) /
        Real.exp (X.p.Kcap * (X.p.q0 * X.p.uSeg n (ℓ.level + 1))) := by
  classical
  let l := X.p.uSeg n (ℓ.level + 1)
  let w := ℓ.coarse.1
  let bad (v : Fin N) (z : Fin l → Word5 N X.p.q0) : Prop := ∃ y,
    Real.exp (X.p.Kcap * (X.p.q0 * l)) < (N : ℝ) *
      (normalize5 (fun a => (X.P.prior.partner v w).w a *
        ∏ s : Fin l, (X.segLaw v a).w (z s)) X.y₀).w y
  let R (v : Fin N) := FinProb.bind (X.P.prior.partner v w)
    (fun a => FinProb.pi fun _ : Fin l => X.segLaw v a)
  have hbad (b : X.Base) : X.capFail b ℓ ↔
      bad b.1 (fun s => b.2.2 w (Fin.castLE (key_prefix_le_stream X ℓ) s)) := by
    unfold Setup5.capFail Setup5.prior
    rw [funext (colWeight_interior_observed X b ℓ hb (fun _ _ => True))]
    simp only [ite_true]
    rfl
  have heq : X.baseLaw.pr (fun b => X.capFail b ℓ) =
      ∑ v, X.P.prior.parent.w v * (R v).pr (fun az => bad v az.2) := by
    simp_rw [hbad]
    rw [Setup5.baseLaw, pr_bind_indic]
    have hobs (v : Fin N) := coarse_single_prefix_expect X v w l (key_prefix_le_stream X ℓ)
      (fun z => indic (bad v z))
    simp_rw [hobs, pr_indic]
    rfl
  rw [heq]
  calc
    _ ≤ ∑ v, X.P.prior.parent.w v * ((4 / χ ^ 2) * Real.exp (X.p.a 0 * (X.p.q0 * l)) /
        Real.exp (X.p.Kcap * (X.p.q0 * l))) := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_left (interior_prefix_cap X v w l) (X.P.prior.parent.nonneg v)
    _ = _ := by rw [← Finset.sum_mul, X.P.prior.parent.sum_eq_one, one_mul]

/-- A uniform bound for the number of bins read by a boundary key. -/
def capBinBound : ℕ := 3 ^ coarseChunkCount5

def capAtom (χ : ℝ) : ℝ := max 1 (4 / χ ^ 2)

def capRequest (χ : ℝ) : ParamReq5 where
  Kcap x := (capBinBound : ℝ) * x.1 0 + ((capBinBound : ℝ) + 1) * Real.log (capAtom χ) + x.2.2.2.1
  Kpp _ := 0
  Kh _ := 0
  K1 _ := 0
  K2 _ := 0
  KD _ := 0
  Ks _ := 0
  KB _ := 0
  alpha _ := 1
  alpha_pos _ := by norm_num

/-- The fixed cap request pays for the atom bound and every observed bin. -/
theorem cap_exponential_budget (b : ℕ) (hb : b ≤ capBinBound) (x : ℝ) (hx : 1 ≤ x)
    (hκ : (capBinBound : ℝ) * X.p.a 0 + ((capBinBound : ℝ) + 1) * Real.log (capAtom χ) +
      X.p.delta ≤ X.p.Kcap) :
    capAtom χ * (capAtom χ * Real.exp (X.p.a 0 * x)) ^ b /
      Real.exp (X.p.Kcap * x) ≤ Real.exp (-(X.p.delta * x)) := by
  let d := capAtom χ
  let L := Real.log d
  have hd1 : 1 ≤ d := le_max_left _ _
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd1
  have hL : 0 ≤ L := Real.log_nonneg hd1
  have ha : 0 ≤ X.p.a 0 := by rw [X.p.ha0]; norm_num
  have hx0 : 0 ≤ x := by linarith
  have hD : d ≤ Real.exp (L * x) := by
    rw [← Real.exp_log hdpos]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hx hL
    simpa only [mul_one] using h
  have hbase : d * Real.exp (X.p.a 0 * x) ≤ Real.exp ((L + X.p.a 0) * x) := by
    calc
      _ ≤ Real.exp (L * x) * Real.exp (X.p.a 0 * x) := mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hpow : (d * Real.exp (X.p.a 0 * x)) ^ b ≤
      Real.exp ((capBinBound : ℝ) * (L + X.p.a 0) * x) := by
    calc
      _ ≤ Real.exp ((L + X.p.a 0) * x) ^ b := pow_le_pow_left₀ (by positivity) hbase b
      _ = Real.exp ((b : ℝ) * ((L + X.p.a 0) * x)) := (Real.exp_nat_mul _ b).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonneg_right (show (b : ℝ) ≤ capBinBound by exact_mod_cast hb)
          (mul_nonneg (add_nonneg hL ha) hx0)
        nlinarith)
  have hnum : d * (d * Real.exp (X.p.a 0 * x)) ^ b ≤
      Real.exp ((L + (capBinBound : ℝ) * (L + X.p.a 0)) * x) := by
    calc
      _ ≤ Real.exp (L * x) * Real.exp ((capBinBound : ℝ) * (L + X.p.a 0) * x) :=
        mul_le_mul hD hpow (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp ((L + (capBinBound : ℝ) * (L + X.p.a 0)) * x) / Real.exp (X.p.Kcap * x) :=
      div_le_div_of_nonneg_right hnum (Real.exp_pos _).le
    _ = Real.exp (((L + (capBinBound : ℝ) * (L + X.p.a 0)) - X.p.Kcap) * x) := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hcoef : L + (capBinBound : ℝ) * (L + X.p.a 0) - X.p.Kcap ≤ -X.p.delta := by
        dsimp [L, d]
        nlinarith [hκ]
      simpa only [neg_mul] using mul_le_mul_of_nonneg_right hcoef hx0)

/-- The two raw cap estimates have the requested common exponential rate. -/
theorem cap_raw_bound (ℓ : X.Key)
    (hx : 1 ≤ ((X.p.q0 * X.p.uSeg n (ℓ.level + 1) : ℕ) : ℝ))
    (hp : (capRequest χ).Holds X.p) :
    X.baseLaw.pr (fun b => X.capFail b ℓ) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (ℓ.level + 1)))) := by
  let x : ℝ := X.p.q0 * X.p.uSeg n (ℓ.level + 1)
  let d := capAtom χ
  let D : ℝ := 4 / χ ^ 2
  have hd : 1 ≤ d := le_max_left _ _
  have hD : D ≤ d := le_max_right _ _
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hd0 : 0 ≤ d := by linarith
  have hx' : 1 ≤ x := by simpa [x] using hx
  have ha : 0 ≤ X.p.a 0 := by rw [X.p.ha0]; norm_num
  have hκ : (capBinBound : ℝ) * X.p.a 0 + ((capBinBound : ℝ) + 1) * Real.log (capAtom χ) +
      X.p.delta ≤ X.p.Kcap := hp.1
  cases hb : ℓ.coarse.2 with
  | true =>
    have hh := boundary_cap_raw_bound X ℓ hb
    have hnum : D * (D * Real.exp (X.p.a 0 * x)) ^ (binList5 ℓ.coarse).card ≤
        d * (d * Real.exp (X.p.a 0 * x)) ^ (binList5 ℓ.coarse).card := by
      exact mul_le_mul hD
        (pow_le_pow_left₀ (mul_nonneg hD0 (Real.exp_pos _).le)
          (mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le) _)
        (by positivity) hd0
    apply hh.trans
    apply le_trans (div_le_div_of_nonneg_right hnum (Real.exp_pos _).le)
    exact cap_exponential_budget X _ (Lane_sol_s05_h1.binList_card_le ℓ.coarse) x hx' hκ
  | false =>
    have hh := interior_cap_raw_bound X ℓ hb
    have hnum : D * Real.exp (X.p.a 0 * x) ≤ d * (d * Real.exp (X.p.a 0 * x)) ^ 1 := by
      simp only [pow_one]
      calc
        _ ≤ d * Real.exp (X.p.a 0 * x) := mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le
        _ ≤ d * (d * Real.exp (X.p.a 0 * x)) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hd (mul_nonneg hd0 (Real.exp_pos _).le)
    apply hh.trans
    apply le_trans (div_le_div_of_nonneg_right hnum (Real.exp_pos _).le)
    exact cap_exponential_budget X 1 (by exact one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) x hx' hκ

/-- All key-prefix label scales are eventually at least one, uniformly in level. -/
theorem eventually_prefix_scale_one (p : Params5 γ K' χ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ j : ℕ, (1 : ℝ) ≤ (p.q0 : ℝ) * p.uSeg n j := by
  have ht : Tendsto (fun n : ℕ => 4 * p.K1 * Real.log (p.m n : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp (Lane_sol_s05_h1.tendsto_m p)).const_mul_atTop (mul_pos (by norm_num) p.hK1)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (ht.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨n₀, ?_⟩
  intro n hn j
  calc
    _ ≤ 4 * p.K1 * Real.log (p.m n : ℝ) := hn₀ n hn
    _ ≤ (p.q0 : ℝ) * p.uSeg n 0 := Lane_sol_s05_h1.uSeg0_lower p n
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by exact_mod_cast Lane_q_s05_hist1b.uSeg_mono5 p n 0 j (Nat.zero_le _)) (Nat.cast_nonneg _)

end
end HypercubeRamsey.Lane_sol_s05_hist1b
