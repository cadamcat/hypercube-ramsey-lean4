import HypercubeRamsey.S08.L81.SelectionNodes_q_s08_sel

noncomputable section
namespace HypercubeRamsey.Lane_sol_s08_sel
open HypercubeRamsey.S08 Classical OAI.HypercubeRamsey
open scoped BigOperators
variable {η₀ β p : ℝ} {h : ℕ}
set_option maxHeartbeats 800000

private theorem pi_expect_equiv {I J A : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A]
    (P : I → FinProb A) (e : J ≃ I) (F : (J → A) → ℝ) :
    (FinProb.pi P).expect (fun z => F (fun j => z (e j))) =
      (FinProb.pi (fun j => P (e j))).expect F := by
  classical
  let E : (I → A) ≃ (J → A) :=
    { toFun := fun z j => z (e j)
      invFun := fun z i => z (e.symm i)
      left_inv := by intro z; funext i; simp
      right_inv := by intro z; funext j; simp }
  apply Fintype.sum_equiv E
  intro z
  change (∏ i, (P i).w (z i)) * F (E z) = (∏ j, (P (e j)).w (E z j)) * F (E z)
  congr 1
  exact (Fintype.prod_equiv e _ _ (by intro j; rfl)).symm

private theorem pi_expect_injective {I J A : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A]
    (P : I → FinProb A) (f : J → I) (hf : Function.Injective f) (F : (J → A) → ℝ) :
    (FinProb.pi P).expect (fun z => F (fun j => z (f j))) =
      (FinProb.pi (fun j => P (f j))).expect F := by
  classical
  let s : Finset I := Finset.univ.image f
  let e : J ≃ {i // i ∈ s} := Equiv.ofBijective
    (fun j => ⟨f j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩)
    ⟨by intro j k h; exact hf (congrArg Subtype.val h), by
      intro i
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.2
      exact ⟨j, Subtype.ext hj⟩⟩
  calc
    _ = (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).expect
        (fun z => F (fun j => z (e j))) :=
      FinProb.pi_marginal_expect P s _
    _ = _ := pi_expect_equiv (fun i : {i // i ∈ s} => P i.1) e F

theorem pi_sum_expect {I J A : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A]
    (P : I → FinProb A) (Q : J → FinProb A) (F : (I → A) → (J → A) → ℝ) :
    (FinProb.pi (Sum.elim P Q)).expect (fun z => F (fun i => z (.inl i)) (fun j => z (.inr j))) =
      ∑ x, (FinProb.pi P).w x * (FinProb.pi Q).expect (F x) := by
  classical
  let E := Equiv.sumArrowEquivProdArrow I J A
  unfold FinProb.expect
  rw [← Equiv.sum_comp E.symm, Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro x
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro y
  simp only [FinProb.pi, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    E, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  ring

theorem pi_expect_resample {I A : Type} [Fintype I] [DecidableEq I] [Fintype A]
    (P : I → FinProb A) (i : I) (F : (I → A) → ℝ) :
    (FinProb.pi P).expect F =
      (P i).expect (fun a => (FinProb.pi P).expect (fun z => F (Function.update z i a))) := by
  classical
  let f : I → Unit ⊕ I := fun j => if j = i then .inl () else .inr j
  have hf : Function.Injective f := by
    intro j k hjk
    by_cases hj : j = i <;> by_cases hk : k = i <;> simp_all [f]
  let Q : Unit ⊕ I → FinProb A := Sum.elim (fun _ => P i) P
  have h := pi_expect_injective Q f hf F
  have hQ : (fun j => Q (f j)) = P := by
    funext j
    by_cases hj : j = i <;> simp [Q, f, hj]
  rw [hQ] at h
  rw [← h]
  have hG : (fun z : Unit ⊕ I → A => F (fun j => z (f j))) = fun z => F (Function.update (fun j => z (.inr j)) i (z (.inl ()))) := by
    funext z
    congr 1
    funext j
    by_cases hj : j = i <;> simp [f, Function.update, hj]
  rw [hG]
  have hsum := pi_sum_expect (fun _ : Unit => P i) P
    (fun x y => F (Function.update y i (x ())))
  simp only [FinProb.expect, FinProb.pi] at hsum ⊢
  dsimp only [Q]
  rw [hsum]
  change (∑ z : Unit → A, (∏ u, (P i).w (z u)) *
    (FinProb.pi P).expect (fun y => F (Function.update y i (z ())))) = _
  let E : (Unit → A) ≃ A := Equiv.funUnique Unit A
  apply Fintype.sum_equiv E
  intro z
  simp [E, FinProb.expect, FinProb.pi]

private theorem Mden_list_reindex (D : Ctx η₀ β p h) (Θ : D.Hist) (g : D.KeyT)
    (L : D.LList g) (t : D.Tags) (c : D.CrossSub g → D.M.ι × Fin D.N)
    (e : Fin L.1.card ≃ L.1) :
    D.Mden Θ g (D.listInt t g L, c) =
      D.Mden Θ g (fun j : Fin L.1.card => some (t g (e j)), c) := by
  unfold Ctx.Mden
  apply Finset.sum_congr rfl
  intro ξ _
  congr 1
  unfold Ctx.Fcand
  congr 2
  have hp : (∏ ℓ : D.Loc, D.intRatio Θ g ξ (D.listInt t g L ℓ)) =
      ∏ ℓ ∈ L.1, D.intRatio Θ g ξ (some (t g ℓ)) := by
    simp only [Ctx.listInt]
    simp_rw [apply_ite]
    simp only [Ctx.intRatio, Option.elim_none, Option.elim_some]
    simpa only [Finset.univ_inter] using Finset.prod_ite_mem Finset.univ L.1 (fun ℓ =>
      (D.tilt (Function.update Θ g ξ) g).w (t g ℓ) / (D.refInt Θ g).w (t g ℓ))
  rw [hp]
  calc
    _ = ∏ ℓ : L.1, D.intRatio Θ g ξ (some (t g ℓ)) := by
      rw [Finset.univ_eq_attach]
      exact (Finset.prod_attach L.1 (fun ℓ => D.intRatio Θ g ξ (some (t g ℓ)))).symm
    _ = _ := (Fintype.prod_equiv e _ _ (by intro j; rfl)).symm

theorem tag_list_average (D : Ctx η₀ β p h) (Θ : D.Hist) (g : D.KeyT) (L : D.LList g) :
    (D.tagLawAll Θ).expect (fun t => D.qL Θ g (D.listInt t g L) (D.listCrossTag t g L)) =
      D.qgk Θ g L.1.card := by
  classical
  let e : Fin L.1.card ≃ L.1 :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe L.1)).symm
  let f : Fin L.1.card ⊕ D.CrossSub g → D.KeyT × D.Loc :=
    Sum.elim (fun j => (g, (e j).1)) (fun u => (u.1, L.2 u))
  have hg : ∀ u : D.CrossSub g, u.1 ≠ g := by
    intro u heq
    have hu := u.2
    have hdiag : keyDist g g = 0 := by simp [keyDist]
    simp only [crossKeys, Finset.mem_filter, Finset.mem_univ, true_and, heq, hdiag] at hu
    omega
  have hf : Function.Injective f := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        apply congrArg Sum.inl
        apply e.injective
        apply Subtype.ext
        exact congrArg Prod.snd hij
      | inr j => exact False.elim (hg j (congrArg Prod.fst hij).symm)
    | inr i =>
      cases j with
      | inl j => exact False.elim (hg i (congrArg Prod.fst hij))
      | inr j =>
        apply congrArg Sum.inr
        exact Subtype.ext (congrArg Prod.fst hij)
  let F : (Fin L.1.card ⊕ D.CrossSub g → D.M.ι) → ℝ := fun z =>
    ∑ x : D.CrossSub g → Fin D.N,
      (if D.CandGate Θ g then 1 else 0) *
        (∏ u, (D.anchorU Θ u.1 (z (.inr u))).w (x u)) *
        if D.Mden Θ g (fun j : Fin L.1.card => some (z (.inl j)),
          fun u => (z (.inr u), x u)) < D.eps0 then 1 else 0
  have hpoint (t : D.Tags) :
      D.qL Θ g (D.listInt t g L) (D.listCrossTag t g L) =
        F (fun j => t (f j).1 (f j).2) := by
    unfold Ctx.qL
    apply Finset.sum_congr rfl
    intro x _
    rw [Mden_list_reindex D Θ g L t _ e]
    rfl
  simp_rw [hpoint]
  rw [HypercubeRamsey.Lane_q_s08_sel.tagLawAll_expect_coordinates D Θ
    (fun t => F (fun j => t (f j)))]
  have hinj := pi_expect_injective (fun i : D.KeyT × D.Loc => D.tilt Θ i.1) f hf F
  simp only [FinProb.expect, FinProb.pi] at hinj ⊢
  rw [hinj]
  let E := Equiv.sumArrowEquivProdArrow (Fin L.1.card) (D.CrossSub g) D.M.ι
  let C := Equiv.arrowProdEquivProdArrow (D.CrossSub g) (fun _ => D.M.ι) (fun _ => Fin D.N)
  change (∑ z, (∏ j, (D.tilt Θ (f j).1).w (z j)) * F z) = _
  rw [← Equiv.sum_comp E.symm, Fintype.sum_prod_type]
  unfold Ctx.qgk Ctx.trueW
  apply Fintype.sum_congr
  intro t
  rw [← Equiv.sum_comp C.symm, Fintype.sum_prod_type]
  change (∑ ct, (∏ j, (D.tilt Θ (f j).1).w (E.symm (t, ct) j)) * F (E.symm (t, ct))) = _
  simp only [Fintype.prod_sum_type]
  simp only [F, E, f, Sum.elim_inl, Sum.elim_inr,
    Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  simp_rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro ct
  apply Fintype.sum_congr
  intro x
  change _ = (if D.CandGate Θ g then 1 else 0) *
    ((∏ j, (D.tilt Θ g).w (t j)) *
    ∏ u, (D.tilt Θ u.1).w (ct u) * (D.anchorU Θ u.1 (ct u)).w (x u)) * _
  have hC : C.symm (ct, x) = (fun u => (ct u, x u)) := rfl
  rw [hC, Finset.prod_mul_distrib]
  ring_nf
  congr 1

private theorem keyDist_geodesic {η₀ : ℝ} {n : ℕ} (g h : Key η₀ n) (hne : 0 < keyDist g h) :
    ∃ z, keyDist g z + 1 = keyDist g h ∧ keyDist z h = 1 := by
  classical
  have hsumpos : 0 < ∑ r, Nat.dist (g r).val (h r).val := by
    simpa [keyDist] using hne
  obtain ⟨r, _, hrne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega :
    (∑ r, Nat.dist (g r).val (h r).val) ≠ 0)
  have hdiff : (g r).val ≠ (h r).val := by
    intro heq
    apply hrne
    simp [heq]
  by_cases hlt : (h r).val < (g r).val
  · let v : Fin (lC n + 1) := ⟨(h r).val + 1, by omega⟩
    let z : Key η₀ n := Function.update h r v
    have hmove : Nat.dist (g r).val v.val + 1 = Nat.dist (g r).val (h r).val := by
      have hvle : v.val ≤ (g r).val := by simp [v]; omega
      have hhle : (h r).val ≤ (g r).val := Nat.le_of_lt hlt
      rw [Nat.dist_eq_sub_of_le_right hvle, Nat.dist_eq_sub_of_le_right hhle]
      simp [v]
      omega
    have hstep : Nat.dist v.val (h r).val = 1 := by
      have hle : (h r).val ≤ v.val := by simp [v]
      rw [Nat.dist_eq_sub_of_le_right hle]
      norm_num [v]
    have hsplit (a k : Key η₀ n) :
        keyDist a k = Nat.dist (a r).val (k r).val +
          ∑ i ∈ Finset.univ.erase r, Nat.dist (a i).val (k i).val := by
      unfold keyDist
      exact (Finset.add_sum_erase Finset.univ
        (fun i => Nat.dist (a i).val (k i).val) (Finset.mem_univ r)).symm
    have hother :
        (∑ i ∈ Finset.univ.erase r, Nat.dist (g i).val (z i).val) =
          ∑ i ∈ Finset.univ.erase r, Nat.dist (g i).val (h i).val := by
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≠ r := Finset.ne_of_mem_erase hi
      simp [z, Function.update_of_ne hir]
    have hother' :
        (∑ i ∈ Finset.univ.erase r, Nat.dist (z i).val (h i).val) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hir : i ≠ r := Finset.ne_of_mem_erase hi
      simp [z, Function.update_of_ne hir]
    refine ⟨z, ?_, ?_⟩
    · rw [hsplit g z, hsplit g h, hother]
      simp only [z, Function.update_self]
      omega
    · rw [hsplit z h, hother']
      simpa [z, Function.update_self] using hstep
  · have hlt' : (g r).val < (h r).val := by omega
    let v : Fin (lC n + 1) := ⟨(h r).val - 1, by omega⟩
    let z : Key η₀ n := Function.update h r v
    have hmove : Nat.dist (g r).val v.val + 1 = Nat.dist (g r).val (h r).val := by
      have hgle : (g r).val ≤ v.val := by simp [v]; omega
      have hghle : (g r).val ≤ (h r).val := Nat.le_of_lt hlt'
      rw [Nat.dist_eq_sub_of_le hgle, Nat.dist_eq_sub_of_le hghle]
      simp [v]
      omega
    have hstep : Nat.dist v.val (h r).val = 1 := by
      have hle : v.val ≤ (h r).val := by simp [v]
      rw [Nat.dist_eq_sub_of_le hle]
      norm_num [v]
      omega
    have hsplit (a k : Key η₀ n) :
        keyDist a k = Nat.dist (a r).val (k r).val +
          ∑ i ∈ Finset.univ.erase r, Nat.dist (a i).val (k i).val := by
      unfold keyDist
      exact (Finset.add_sum_erase Finset.univ
        (fun i => Nat.dist (a i).val (k i).val) (Finset.mem_univ r)).symm
    have hother :
        (∑ i ∈ Finset.univ.erase r, Nat.dist (g i).val (z i).val) =
          ∑ i ∈ Finset.univ.erase r, Nat.dist (g i).val (h i).val := by
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≠ r := Finset.ne_of_mem_erase hi
      simp [z, Function.update_of_ne hir]
    have hother' :
        (∑ i ∈ Finset.univ.erase r, Nat.dist (z i).val (h i).val) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hir : i ≠ r := Finset.ne_of_mem_erase hi
      simp [z, Function.update_of_ne hir]
    refine ⟨z, ?_, ?_⟩
    · rw [hsplit g z, hsplit g h, hother]
      simp only [z, Function.update_self]
      omega
    · rw [hsplit z h, hother']
      simpa [z, Function.update_self] using hstep


theorem keyBall_card {n : ℕ} (g : Key η₀ n) (R : ℕ) :
    (keyBall g R).card ≤ (2 * sC η₀ n + 1) ^ R := by
  classical
  apply HypercubeRamsey.S07.finiteBall_card_le_of_geodesic keyDist g R (2 * sC η₀ n)
  · intro x y hxy
    funext r
    apply Fin.ext
    apply Nat.eq_of_dist_eq_zero
    have ht : Nat.dist (x r).val (y r).val ≤ keyDist x y :=
      Finset.single_le_sum (f := fun i => Nat.dist (x i).val (y i).val)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ r)
    omega
  · exact keyDist_geodesic
  · intro x
    exact HypercubeRamsey.S08.keyDistOne_card_bound x

theorem hidden_degree (D : Ctx η₀ β p h) (g : D.KeyT) :
    (Finset.univ.filter fun j => j ≠ g ∧ ¬ Disjoint (keyBall g 2) (keyBall j 2)).card ≤
      (2 * sC η₀ D.n + 1) ^ 4 := by
  classical
  apply le_trans (Finset.card_le_card (t := keyBall g 4) ?_) (keyBall_card g 4)
  intro j hj
  have hn := (Finset.mem_filter.mp hj).2.2
  obtain ⟨u, hu, hu'⟩ := Finset.not_disjoint_iff.mp hn
  have hgu := (Finset.mem_filter.mp hu).2
  have hju := (Finset.mem_filter.mp hu').2
  have htri : keyDist g j ≤ keyDist g u + keyDist u j := by
    unfold keyDist
    simpa only [Finset.sum_add_distrib] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => Nat.dist.triangle_inequality (g i).val (u i).val (j i).val)
  have hsym : keyDist u j = keyDist j u := by simp [keyDist, Nat.dist_comm]
  simp only [keyBall, Finset.mem_filter, Finset.mem_univ, true_and]
  omega


private theorem qgk_nonneg (D : Ctx η₀ β p h) (Θ : D.Hist) (g : D.KeyT) (k : ℕ) :
    0 ≤ D.qgk Θ g k := by
  unfold Ctx.qgk Ctx.trueW
  apply Finset.sum_nonneg
  intro t _
  apply Finset.sum_nonneg
  intro c _
  apply mul_nonneg
  · apply mul_nonneg (ind_nonneg _)
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun j _ => (D.tilt Θ g).nonneg _)
    · exact Finset.prod_nonneg (fun u _ => mul_nonneg ((D.tilt Θ u.1).nonneg _) ((D.anchorU Θ u.1 _).nonneg _))
  · exact ind_nonneg _

theorem hidden_raw_bound (D : Ctx η₀ β p h) (c' : ℝ)
    (hGT : D.GateTail c') (hDT : D.DenTail) (g : D.KeyT) :
    D.rawHidden.pr (fun Θ => D.HBad Θ g) ≤
      Real.exp (-(D.n : ℝ) ^ c') + (TC η₀ D.n + 1 : ℕ) * Real.sqrt D.eps0 := by
  classical
  have heps : 0 < D.eps0 := Real.exp_pos _
  have hsqrt : 0 < Real.sqrt D.eps0 := Real.sqrt_pos.2 heps
  have hqmean (k : ℕ) : D.rawHidden.expect (fun Θ => D.qgk Θ g k) ≤ D.eps0 := by
    rw [show D.rawHidden = FinProb.pi (fun _ : D.KeyT => D.R') from rfl]
    have hr := pi_expect_resample (fun _ : D.KeyT => D.R') g (fun Θ => D.qgk Θ g k)
    simp only [FinProb.expect, FinProb.pi] at hr ⊢
    rw [hr]
    change (∑ ξ, D.R'.w ξ * ∑ Θ, D.rawHidden.w Θ * D.qgk (Function.update Θ g ξ) g k) ≤ _
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hrew : (∑ Θ, ∑ ξ, D.R'.w ξ * (D.rawHidden.w Θ * D.qgk (Function.update Θ g ξ) g k)) =
        D.rawHidden.expect (fun Θ => D.R'.expect (fun ξ => D.qgk (Function.update Θ g ξ) g k)) := by
      unfold FinProb.expect
      simp_rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro Θ
      apply Fintype.sum_congr
      intro ξ
      ring
    rw [hrew]
    calc
      _ ≤ D.rawHidden.expect (fun _ => D.eps0) := FinProb.expect_mono _ (fun Θ => hDT Θ g k)
      _ = D.eps0 := by simp [FinProb.expect, ← Finset.sum_mul, D.rawHidden.sum_eq_one]
  have hkprob (k : ℕ) :
      D.rawHidden.pr (fun Θ => Real.sqrt D.eps0 < D.qgk Θ g k) ≤ Real.sqrt D.eps0 := by
    apply le_trans (FinProb.pr_mono _ _ _ (fun Θ hΘ => hΘ.le))
    apply le_trans (FinProb.markov _ _ _ (fun Θ => qgk_nonneg D Θ g k) hsqrt)
    apply (div_le_iff₀ hsqrt).2
    calc
      _ ≤ D.eps0 := hqmean k
      _ = Real.sqrt D.eps0 * Real.sqrt D.eps0 := (Real.mul_self_sqrt heps.le).symm
  have hE : (fun Θ : D.Hist => ∃ k ≤ TC η₀ D.n, Real.sqrt D.eps0 < D.qgk Θ g k) =
      (fun Θ => ∃ k : Fin (TC η₀ D.n + 1), Real.sqrt D.eps0 < D.qgk Θ g k.val) := by
    funext Θ
    apply propext
    constructor
    · rintro ⟨k, hk, hq⟩; exact ⟨⟨k, by omega⟩, hq⟩
    · rintro ⟨k, hq⟩; exact ⟨k.val, by omega, hq⟩
  calc
    _ ≤ D.rawHidden.pr (fun Θ => ¬ D.BaseGates Θ g) +
        D.rawHidden.pr (fun Θ => ∃ k ≤ TC η₀ D.n, Real.sqrt D.eps0 < D.qgk Θ g k) :=
      FinProb.pr_union _ _ _
    _ ≤ Real.exp (-(D.n : ℝ) ^ c') +
        ∑ k : Fin (TC η₀ D.n + 1), D.rawHidden.pr (fun Θ => Real.sqrt D.eps0 < D.qgk Θ g k.val) := by
      rw [hE]
      exact add_le_add (hGT g) (HypercubeRamsey.Lane_q_s08_sel.pr_exists_le_sum _ _)
    _ ≤ _ := by
      apply add_le_add_right
      calc
        _ ≤ ∑ _k : Fin (TC η₀ D.n + 1), Real.sqrt D.eps0 :=
          Finset.sum_le_sum (fun k _ => hkprob k.val)
        _ = _ := by simp

private theorem nat_poly_exp_decay (c b : ℝ) (hc : 0 < c) (hb : 0 < b) (k : ℝ) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-b * (n : ℝ) ^ c))
      Filter.atTop (nhds 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k / c) b hb).comp
    ((_root_.tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop)
  apply ht.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hnpos.le]
  congr 2
  field_simp


theorem tau_bounds (hη₀ : 0 < η₀) : 0 < tau8 η₀ ∧ tau8 η₀ ≤ 1 := by
  unfold tau8
  constructor
  · exact div_pos (lt_min (by linarith) (by norm_num)) (by norm_num)
  · have h := min_le_right (η₀ / 2) (4 / 100 : ℝ)
    linarith

theorem scales_le (hη₀ : 0 < η₀) {n : ℕ} (hn : 1 ≤ n) :
    TC η₀ n ≤ sC η₀ n ∧ sC η₀ n ≤ n := by
  have hτ := tau_bounds hη₀
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · apply Nat.ceil_mono
    exact Real.rpow_le_rpow_of_exponent_le hnR (by linarith : tau8 η₀ / 8 ≤ tau8 η₀)
  · apply Nat.ceil_le.mpr
    simpa using Real.rpow_le_rpow_of_exponent_le hnR hτ.2

private theorem one_sub_pow_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    1 - (m : ℝ) * x ≤ (1 - x) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp := pow_le_one₀ (sub_nonneg.mpr hx1) (sub_le_self 1 hx0) (n := m)
    rw [pow_succ]
    push_cast
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hp)]

theorem hidden_numeric (c' : ℝ) (hc' : 0 < c') (hη₀ : 0 < η₀) (hh : 1 ≤ h) :
    ∃ cH > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let x := 2 * Real.exp (-(n : ℝ) ^ cH)
      0 ≤ x ∧ x < 1 ∧
      Real.exp (-(n : ℝ) ^ c') + (TC η₀ n + 1 : ℕ) *
        Real.sqrt (Real.exp (-((1 / 10000 : ℝ) * h * sC η₀ n * Real.log n))) ≤
          x * (1 - x) ^ ((2 * sC η₀ n + 1) ^ 4) := by
  let cH := min c' (tau8 η₀) / 4
  have hτ := tau_bounds hη₀
  have hcH : 0 < cH := by dsimp [cH]; exact div_pos (lt_min hc' hτ.1) (by norm_num)
  have hgc : 0 < c' - cH := by have := min_le_left c' (tau8 η₀); dsimp [cH]; linarith
  have hgt : 0 < tau8 η₀ - cH := by have := min_le_right c' (tau8 η₀); dsimp [cH]; linarith
  have ht (a : ℝ) (ha : 0 < a) :=
    (_root_.tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hd1 := nat_poly_exp_decay cH 1 hcH (by norm_num) 4
  have hd3 := nat_poly_exp_decay cH 3 hcH (by norm_num) 1
  have he := (ht (c' - cH) hgc).eventually (Filter.eventually_ge_atTop 4)
  have he' := (ht (tau8 η₀ - cH) hgt).eventually (Filter.eventually_ge_atTop 80000)
  have hsmall1 := hd1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 324 by norm_num))
  have hsmall3 := hd3.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_ge_atTop (4 : ℕ)).and (he.and (he'.and (hsmall1.and hsmall3))))
  refine ⟨cH, hcH, n₀, ?_⟩
  intro n hn
  obtain ⟨hn4, hgapc, hgapt, hsmall, hsmall'⟩ := hn₀ n hn
  dsimp only [Function.comp_apply] at hgapc hgapt
  simp only [neg_one_mul, Real.rpow_one] at hsmall hsmall'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hs := scales_le hη₀ (by omega : 1 ≤ n)
  have hsR : (sC η₀ n : ℝ) ≤ n := by exact_mod_cast hs.2
  have hTR : (TC η₀ n : ℝ) ≤ n := by exact_mod_cast hs.1.trans hs.2
  have hlog : 1 ≤ Real.log n := by
    have h4 : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have hlog4 : 1 ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      nlinarith [Real.log_two_gt_d9]
    exact hlog4.trans (Real.log_le_log (by norm_num) h4)
  have hpowc : 4 * (n : ℝ) ^ cH ≤ (n : ℝ) ^ c' := by
    have hp : cH + (c' - cH) = c' := by ring
    rw [← hp, Real.rpow_add hnpos]
    nlinarith [Real.rpow_nonneg hnpos.le cH]
  have hpowt : 80000 * (n : ℝ) ^ cH ≤ (n : ℝ) ^ tau8 η₀ := by
    have hp : cH + (tau8 η₀ - cH) = tau8 η₀ := by ring
    rw [← hp, Real.rpow_add hnpos]
    nlinarith [Real.rpow_nonneg hnpos.le cH]
  have hslo : (n : ℝ) ^ tau8 η₀ ≤ sC η₀ n := Nat.le_ceil _
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hexpt : 4 * (n : ℝ) ^ cH ≤ (1 / 20000 : ℝ) * h * sC η₀ n * Real.log n := by
    have hmul := mul_le_mul hslo hlog (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : 0 ≤ (sC η₀ n : ℝ))
    have hhlo := mul_le_mul_of_nonneg_right hhR
      (show 0 ≤ (sC η₀ n : ℝ) * Real.log n by positivity)
    nlinarith
  have hsqrt : Real.sqrt (Real.exp (-((1 / 10000 : ℝ) * h * sC η₀ n * Real.log n))) ≤
      Real.exp (-4 * (n : ℝ) ^ cH) := by
    rw [← Real.exp_half]
    apply Real.exp_le_exp.mpr
    linarith
  have hprob : Real.exp (-(n : ℝ) ^ c') + (TC η₀ n + 1 : ℕ) *
      Real.sqrt (Real.exp (-((1 / 10000 : ℝ) * h * sC η₀ n * Real.log n))) ≤
      Real.exp (-(n : ℝ) ^ cH) := by
    have h3n : (TC η₀ n + 1 : ℕ) + (1 : ℝ) ≤ 3 * n := by push_cast; linarith
    have hprod : 3 * (n : ℝ) * Real.exp (-3 * (n : ℝ) ^ cH) ≤ 1 := by
      nlinarith [hsmall']
    calc
      _ ≤ (1 + (TC η₀ n + 1 : ℕ)) * Real.exp (-4 * (n : ℝ) ^ cH) := by
        have hec := Real.exp_le_exp.mpr (neg_le_neg hpowc)
        rw [← neg_mul] at hec
        have het := mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg (TC η₀ n + 1))
        nlinarith
      _ ≤ 3 * n * Real.exp (-4 * (n : ℝ) ^ cH) := by gcongr; linarith
      _ = (3 * n * Real.exp (-3 * (n : ℝ) ^ cH)) * Real.exp (-(n : ℝ) ^ cH) := by
        have he : Real.exp (-4 * (n : ℝ) ^ cH) =
            Real.exp (-3 * (n : ℝ) ^ cH) * Real.exp (-(n : ℝ) ^ cH) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [he]; ring
      _ ≤ Real.exp (-(n : ℝ) ^ cH) := by
        simpa using mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-(n : ℝ) ^ cH)).le
  let x := 2 * Real.exp (-(n : ℝ) ^ cH)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hdeg : (((2 * sC η₀ n + 1) ^ 4 : ℕ) : ℝ) ≤ 81 * (n : ℝ) ^ (4 : ℝ) := by
    push_cast
    norm_num only [Real.rpow_ofNat]
    have hh' : 2 * (sC η₀ n : ℝ) + 1 ≤ 3 * n := by linarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (sC η₀ n : ℝ) + 1) hh' 4
    nlinarith [hp]
  have hdx : (((2 * sC η₀ n + 1) ^ 4 : ℕ) : ℝ) * x ≤ 1 / 2 := by
    dsimp [x]
    have hb := mul_le_mul_of_nonneg_right hdeg (show 0 ≤ 2 * Real.exp (-(n : ℝ) ^ cH) by positivity)
    nlinarith
  have hdegl : (1 : ℝ) ≤ (((2 * sC η₀ n + 1) ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ (2 * sC η₀ n + 1) ^ 4 from one_le_pow₀ (by omega))
  have hxlt : x < 1 := by nlinarith
  refine ⟨hx, hxlt, hprob.trans ?_⟩
  have hp := one_sub_pow_lower hx hxlt.le ((2 * sC η₀ n + 1) ^ 4)
  have hhalf : (1 / 2 : ℝ) ≤ (1 - x) ^ ((2 * sC η₀ n + 1) ^ 4) := by linarith
  change Real.exp (-(n : ℝ) ^ cH) ≤ x * _
  have hm := mul_le_mul_of_nonneg_left hhalf hx
  dsimp [x] at hm
  nlinarith


private theorem expect_prod {A B : Type} [Fintype A] [Fintype B]
    (P : FinProb A) (Q : FinProb B) (F : A × B → ℝ) :
    (P.prod Q).expect F = P.expect (fun a => Q.expect (fun b => F (a, b))) := by
  unfold FinProb.expect FinProb.prod
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  ring

theorem preLaw_slice_expect (D : Ctx η₀ β p h) (g : D.KeyT)
    (F : D.Pos → D.Hist → D.Tags → (D.Loc → Bool) → ℝ) :
    D.preLaw.expect (fun q => F q.1.2 q.1.1 q.2.1.1 (q.2.1.2 g)) =
      (((hdP η₀ D.n).posLaw.prod (D.posLaw.prod
        (FinProb.bind D.hiddenLaw (fun Θ => D.tagLawAll Θ)))).prod (hdP η₀ D.n).actLaw).expect
        (fun z => F (Function.update z.1.2.1 g z.1.1) z.1.2.2.1 z.1.2.2.2 z.2) := by
  classical
  rw [HypercubeRamsey.Lane_q_s08_sel.preLaw_expect_noTie D
    (fun P Θ t A => F P Θ t (A g))]
  dsimp only
  simp only [expect_prod]
  simp_rw [show D.actLaw = FinProb.pi (fun _ : D.KeyT => (hdP η₀ D.n).actLaw) from rfl,
    HypercubeRamsey.Lane_q_s08_sel.pi_expect_coordinate (hdP η₀ D.n).actLaw g]
  exact pi_expect_resample (fun _ : D.KeyT => (hdP η₀ D.n).posLaw) g _


theorem key_card_le (D : Ctx η₀ β p h) (hGF : GridFacts η₀ D.n) :
    Fintype.card D.KeyT ≤ 2 ^ D.n := by
  have hl : lC D.n + 1 ≤ 2 ^ lC D.n := by
    simpa using Nat.choose_succ_le_two_pow (lC D.n) 1
  have hm : mC η₀ D.n ≤ D.n := by have := hGF.split; omega
  calc
    _ = (lC D.n + 1) ^ sC η₀ D.n := by simp [Ctx.KeyT, Key]
    _ ≤ (2 ^ lC D.n) ^ sC η₀ D.n := Nat.pow_le_pow_left hl _
    _ = 2 ^ mC η₀ D.n := by rw [← pow_mul]; simp [mC, Nat.mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hm

theorem preLaw_tags_expect (D : Ctx η₀ β p h) (F : D.Pos → D.Hist → D.Tags → ℝ) :
    D.preLaw.expect (fun q => F q.1.2 q.1.1 q.2.1.1) =
      D.posLaw.expect (fun P => D.hiddenLaw.expect (fun Θ => (D.tagLawAll Θ).expect (F P Θ))) := by
  rw [HypercubeRamsey.Lane_q_s08_sel.preLaw_expect_noTie D (fun P Θ t _ => F P Θ t)]
  dsimp only
  simp only [expect_prod]
  simp only [FinProb.expect, FinProb.bind, Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul, D.actLaw.sum_eq_one, one_mul]
  simp_rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro P
  apply Fintype.sum_congr
  intro Θ
  apply Fintype.sum_congr
  intro t
  ring

theorem hiddenLaw_support (D : Ctx η₀ β p h)
    (hAvoid : 0 < D.rawHidden.pr (fun Θ => ∀ g, ¬ D.HBad Θ g)) (Θ : D.Hist)
    (hw : D.hiddenLaw.w Θ ≠ 0) : ∀ g, ¬ D.HBad Θ g := by
  by_contra hΘ
  apply hw
  simp [Ctx.hiddenLaw, condOr, hAvoid, FinProb.cond, hΘ]

theorem few_bad_tags_bound (D : Ctx η₀ β p h) (Θ : D.Hist) (P : D.Pos)
    (hΘ : ∀ g, ¬ D.HBad Θ g) (hP : D.PosOK P)
    (hCount : D.ListCount) (hProb : D.BadListProb) :
    (D.tagLawAll Θ).pr (fun t => ¬ D.FewBad Θ P t) ≤
      (Fintype.card D.CellT : ℝ) *
        (Real.exp (25 * (sC η₀ D.n + TC η₀ D.n : ℝ) * Real.log D.n) *
          Real.sqrt (Real.sqrt D.eps0)) ^ D.n := by
  classical
  let δ := Real.sqrt (Real.sqrt D.eps0)
  let Ln := Real.exp (25 * (sC η₀ D.n + TC η₀ D.n : ℝ) * Real.log D.n)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hcell (c : D.CellT) :
      (D.tagLawAll Θ).pr (fun t => D.n ≤ (D.family Θ P t c).length) ≤ (Ln * δ) ^ D.n := by
    let pool := Finset.univ.filter (fun L : D.LList c.1 => D.Cand P c L)
    let Tup := Fin D.n → pool
    let ls : Tup → List (D.LList c.1) := fun r => List.ofFn (fun i => (r i).1)
    let E : Tup → D.Tags → Prop := fun r t =>
      (ls r).Pairwise (fun L L' => Disjoint (D.listIds c.1 L) (D.listIds c.1 L')) ∧
        ∀ L ∈ ls r, D.BadList Θ t c L
    have hsub (t : D.Tags) (ht : D.n ≤ (D.family Θ P t c).length) : ∃ r, E r t := by
      let fam := D.family Θ P t c
      let r : Tup := fun i => ⟨fam.get ⟨i.val, i.isLt.trans_le ht⟩, by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact HypercubeRamsey.Lane_q_s08_sel.family_candidate D Θ P t c (List.get_mem _ _)⟩
      refine ⟨r, ?_, ?_⟩
      · apply List.pairwise_ofFn.mpr
        intro i j hij
        exact (HypercubeRamsey.Lane_q_s08_sel.family_pairwise_disjoint D Θ P t c).rel_get_of_lt
          (show (⟨i.val, i.isLt.trans_le ht⟩ : Fin fam.length) < ⟨j.val, j.isLt.trans_le ht⟩ from hij)
      · intro L hL
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hL
        exact HypercubeRamsey.Lane_q_s08_sel.family_badList D Θ P t c (List.get_mem _ _)
    have hpr (r : Tup) : (D.tagLawAll Θ).pr (E r) ≤ δ ^ D.n := by
      by_cases hp : (ls r).Pairwise (fun L L' => Disjoint (D.listIds c.1 L) (D.listIds c.1 L'))
      · apply le_trans (FinProb.pr_mono _ _ _ (fun t ht => ht.2))
        have hb := HypercubeRamsey.Lane_q_s08_sel.badListList_probability_le D Θ P hΘ hProb c (ls r) ?_ hp
        · simpa [ls, δ] using hb
        · intro L hL
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hL
          exact (Finset.mem_filter.mp (r i).2).2
      · have hz : (D.tagLawAll Θ).pr (E r) = 0 := by simp [FinProb.pr, E, hp]
        rw [hz]
        positivity
    have hpc : (pool.card : ℝ) ≤ Ln := by
      apply hCount P c
      intro e he j
      exact (hP e.1 e.2 j).2
    have hcard : (Fintype.card Tup : ℝ) = (pool.card : ℝ) ^ D.n := by
      simp [Tup, Fintype.card_coe]
    calc
      _ ≤ (D.tagLawAll Θ).pr (fun t => ∃ r, E r t) := FinProb.pr_mono _ _ _ hsub
      _ ≤ ∑ r : Tup, (D.tagLawAll Θ).pr (E r) :=
        HypercubeRamsey.Lane_q_s08_sel.pr_exists_le_sum _ E
      _ ≤ (Fintype.card Tup : ℝ) * δ ^ D.n := by
        calc
          _ ≤ ∑ _r : Tup, δ ^ D.n := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hpr r)
          _ = _ := by rw [Finset.sum_const, Finset.card_univ]; simp [nsmul_eq_mul]
      _ = (pool.card : ℝ) ^ D.n * δ ^ D.n := by rw [hcard]
      _ ≤ Ln ^ D.n * δ ^ D.n := by gcongr
      _ = _ := (mul_pow _ _ _).symm
  have hsub (t : D.Tags) (ht : ¬ D.FewBad Θ P t) :
      ∃ c : D.CellT, D.n ≤ (D.family Θ P t c).length := by
    simp only [Ctx.FewBad, not_forall, not_lt] at ht
    exact ht
  calc
    _ ≤ (D.tagLawAll Θ).pr (fun t => ∃ c, D.n ≤ (D.family Θ P t c).length) :=
      FinProb.pr_mono _ _ _ hsub
    _ ≤ ∑ c : D.CellT, (D.tagLawAll Θ).pr (fun t => D.n ≤ (D.family Θ P t c).length) :=
      HypercubeRamsey.Lane_q_s08_sel.pr_exists_le_sum _ _
    _ ≤ _ := by
      change _ ≤ (Fintype.card D.CellT : ℝ) * (Ln * δ) ^ D.n
      calc
        _ ≤ ∑ _c : D.CellT, (Ln * δ) ^ D.n := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hcell c)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ]; simp [nsmul_eq_mul]


theorem two_pow_le_exp (n : ℕ) : (2 : ℝ) ^ n ≤ Real.exp n := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) h2 n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem few_bad_numeric (D : Ctx η₀ β p h) (hη₀ : 0 < η₀) (hh : 10 ^ 8 ≤ h)
    (hn : 4 ≤ D.n) (hGF : GridFacts η₀ D.n) :
    (Fintype.card D.CellT : ℝ) *
      (Real.exp (25 * (sC η₀ D.n + TC η₀ D.n : ℝ) * Real.log D.n) *
        Real.sqrt (Real.sqrt D.eps0)) ^ D.n ≤ Real.exp (-(D.n : ℝ)) := by
  have hs := scales_le hη₀ (by omega : 1 ≤ D.n)
  have hs1 : (1 : ℝ) ≤ sC η₀ D.n := by exact_mod_cast hGF.pos.2.2
  have hTS : (TC η₀ D.n : ℝ) ≤ sC η₀ D.n := by exact_mod_cast hs.1
  have hhR : (10 ^ 8 : ℝ) ≤ h := by exact_mod_cast hh
  have hlog : 1 ≤ Real.log D.n := by
    have hlog4 : 1 ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      nlinarith [Real.log_two_gt_d9]
    exact hlog4.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have hcoef : 25 * (sC η₀ D.n + TC η₀ D.n : ℝ) - (h : ℝ) / 40000 * sC η₀ D.n ≤ -3 := by
    have hhS := mul_le_mul_of_nonneg_right hhR (by positivity : 0 ≤ (sC η₀ D.n : ℝ))
    nlinarith
  have hex : (25 * (sC η₀ D.n + TC η₀ D.n : ℝ) - (h : ℝ) / 40000 * sC η₀ D.n) *
      Real.log D.n ≤ -3 := by
    have hc := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ Real.log D.n by linarith)
    linarith
  have hδ : Real.exp (25 * (sC η₀ D.n + TC η₀ D.n : ℝ) * Real.log D.n) *
      Real.sqrt (Real.sqrt D.eps0) ≤ Real.exp (-3) := by
    unfold Ctx.eps0
    rw [← Real.exp_half, ← Real.exp_half, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hex]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ Real.exp (25 * (sC η₀ D.n + TC η₀ D.n : ℝ) * Real.log D.n) *
      Real.sqrt (Real.sqrt D.eps0)) hδ D.n
  have hcard : (Fintype.card D.CellT : ℝ) ≤ Real.exp (2 * D.n) := by
    have hk := key_card_le D hGF
    have hr : Fintype.card D.ResT ≤ 2 ^ D.n := by
      simp only [Ctx.ResT, Res, CubeVertex, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    have hC : Fintype.card D.CellT ≤ 2 ^ D.n * 2 ^ D.n := by
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul hk hr
    calc
      _ ≤ (2 : ℝ) ^ D.n * (2 : ℝ) ^ D.n := by exact_mod_cast hC
      _ ≤ Real.exp D.n * Real.exp D.n := by gcongr <;> exact two_pow_le_exp D.n
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ Real.exp (2 * D.n) * (Real.exp (-3)) ^ D.n := by gcongr
    _ = Real.exp (-(D.n : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

end HypercubeRamsey.Lane_sol_s08_sel
