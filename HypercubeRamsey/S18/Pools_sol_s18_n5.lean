import HypercubeRamsey.S18.Comparisons_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

theorem uniform_pi_sets {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (S : ∀ i, Finset (Ω i)) (hS : ∀ i, (S i).Nonempty) :
    FinLaw.uniform (Finset.univ.filter fun x : ∀ i, Ω i => ∀ i, x i ∈ S i)
      (by
        classical
        refine ⟨fun i => (hS i).choose, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun i => (hS i).choose_spec) =
      FinLaw.pi (fun i => FinLaw.uniform (S i) (hS i)) := by
  classical
  let good := Finset.univ.filter fun x : ∀ i, Ω i => ∀ i, x i ∈ S i
  let e : {x : ∀ i, Ω i // x ∈ good} ≃ (∀ i, {y : Ω i // y ∈ S i}) := {
    toFun := fun x i => ⟨x.1 i, (Finset.mem_filter.mp x.2).2 i⟩
    invFun := fun x => ⟨fun i => (x i).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => (x i).2⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcard : good.card = ∏ i, (S i).card := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_coe, Fintype.card_pi] using h
  apply S16.Lane_q_s16_comp2.finLaw_ext
  intro x
  change (if x ∈ good then 1 / (good.card : ℝ) else 0) =
    ∏ i, (if x i ∈ S i then 1 / ((S i).card : ℝ) else 0)
  by_cases hg : ∀ i, x i ∈ S i
  · have hx : x ∈ good := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩
    simp only [if_pos hx, hg, if_true, hcard, Nat.cast_prod]
    rw [Finset.prod_div_distrib]
    simp
  · have hx : x ∉ good := by simpa [good] using hg
    have hi : ∃ i, x i ∉ S i := not_forall.mp hg
    obtain ⟨i, hi⟩ := hi
    rw [if_neg hx]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem pi_expect_dominate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P Q : ∀ i, FinLaw (Ω i)) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hcomp : ∀ i, ∀ f : Ω i → ℝ, (∀ x, 0 ≤ f x) → (P i).E f ≤ c i * (Q i).E f)
    (f : (∀ i, Ω i) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (FinLaw.pi P).E f ≤ (∏ i, c i) * (FinLaw.pi Q).E f := by
  classical
  have hweight (i : ι) (x : Ω i) : (P i).w x ≤ c i * (Q i).w x := by
    have h := hcomp i (fun y => if y = x then 1 else 0) (by intro y; split_ifs <;> norm_num)
    simpa only [FinLaw.E, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h
  unfold FinLaw.E
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hprod : (FinLaw.pi P).w x ≤ (∏ i, c i) * (FinLaw.pi Q).w x := by
    change (∏ i, (P i).w (x i)) ≤ (∏ i, c i) * (∏ i, (Q i).w (x i))
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun i _ => (P i).nonneg (x i)) (fun i _ => hweight i (x i))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hprod (hf x)


theorem uniform_expect_equiv {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (S : Finset α) (hS : S.Nonempty)
    (f : α → ℝ) :
    (FinLaw.uniform S hS).E f =
      (FinLaw.uniform (S.image e) (hS.image e)).E (fun x => f (e.symm x)) := by
  classical
  unfold FinLaw.E
  rw [← e.symm.sum_comp (fun x => (FinLaw.uniform S hS).w x * f x)]
  apply Finset.sum_congr rfl
  intro x _
  have hm : e.symm x ∈ S ↔ x ∈ S.image e := by
    constructor
    · intro h
      exact Finset.mem_image.mpr ⟨e.symm x, h, e.apply_symm_apply x⟩
    · intro h
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp h
      simpa only [← heq, e.symm_apply_apply] using hy
  have hc : (S.image e).card = S.card := Finset.card_image_of_injective S e.injective
  simp only [FinLaw.uniform, hm, hc]

noncomputable def patchPoolEquiv (D : LateData hPT) :
    (∀ C, D.fresh.Pool C) ≃
      (∀ i : Fin PT.tiling.m, ∀ C : {C : D.geom.Cell // D.geom.cellPatch C = i}, D.fresh.Pool C.1) where
  toFun P _ C := P C.1
  invFun P C := P (D.geom.cellPatch C) ⟨C, rfl⟩
  left_inv _ := rfl
  right_inv P := by
    funext i C
    rcases C with ⟨C, hC⟩
    cases hC
    rfl

noncomputable def patchPermPools (D : LateData hPT) (i : Fin PT.tiling.m) :
    Finset (∀ C : {C : D.geom.Cell // D.geom.cellPatch C = i}, D.fresh.Pool C.1) :=
  Finset.univ.filter fun P =>
    ∀ (C C' : {C : D.geom.Cell // D.geom.cellPatch C = i})
      (s : Fin (D.geom.nslot C.1)) (s' : Fin (D.geom.nslot C'.1)),
      (P C s).1 = (P C' s').1 → C.1 = C'.1 ∧ s.val = s'.val

theorem permPools_patchwise (D : LateData hPT) (P : ∀ C, D.fresh.Pool C) :
    P ∈ permPools D.geom ↔ ∀ i, patchPoolEquiv D P i ∈ patchPermPools D i := by
  classical
  simp only [permPools, patchPermPools, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h i C C' s s' heq
    exact h C.1 C'.1 s s' (C.2.trans C'.2.symm) heq
  · intro h C C' s s' hpatch heq
    exact h (D.geom.cellPatch C) ⟨C, rfl⟩ ⟨C', hpatch.symm⟩ s s' heq

theorem patchPermPools_nonempty (D : LateData hPT) (i : Fin PT.tiling.m) :
    (patchPermPools D i).Nonempty :=
  ⟨patchPoolEquiv D D.l16_valid.pools_nonempty.choose i,
    (permPools_patchwise D _).mp D.l16_valid.pools_nonempty.choose_spec i⟩

theorem permPool_expect_patchwise (D : LateData hPT) (f : (∀ C, D.fresh.Pool C) → ℝ) :
    D.encoding.poolLaw.E f =
      (FinLaw.pi (fun i => FinLaw.uniform (patchPermPools D i) (patchPermPools_nonempty D i))).E
        (fun P => f ((patchPoolEquiv D).symm P)) := by
  classical
  let good : Finset (∀ i : Fin PT.tiling.m,
      ∀ C : {C : D.geom.Cell // D.geom.cellPatch C = i}, D.fresh.Pool C.1) :=
    Finset.univ.filter fun P => ∀ i, P i ∈ patchPermPools D i
  have hi : (permPools D.geom).image (patchPoolEquiv D) = good := by
    ext P
    simp only [Finset.mem_image, good, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact (permPools_patchwise D Q).mp hQ
    · intro hP
      refine ⟨(patchPoolEquiv D).symm P, ?_, by simp⟩
      apply (permPools_patchwise D _).mpr
      simpa using hP
  have he := uniform_expect_equiv (patchPoolEquiv D) (permPools D.geom) D.encoding.pools_nonempty f
  have hU := uniform_pi_sets (patchPermPools D) (patchPermPools_nonempty D)
  change (FinLaw.uniform (permPools D.geom) D.encoding.pools_nonempty).E f = _
  rw [he]
  have hLaw : FinLaw.uniform ((permPools D.geom).image (patchPoolEquiv D))
      (D.encoding.pools_nonempty.image (patchPoolEquiv D)) =
      FinLaw.pi (fun i => FinLaw.uniform (patchPermPools D i) (patchPermPools_nonempty D i)) := by
    rw [← hU]
    congr 1
    ext P
    simp only [hi, good, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hLaw]

theorem iidPool_expect_patchwise (D : LateData hPT) (f : (∀ C, D.fresh.Pool C) → ℝ) :
    D.encoding.iidLaw.E f =
      (FinLaw.pi (fun i : Fin PT.tiling.m =>
        FinLaw.uniform (Finset.univ : Finset (∀ C : {C : D.geom.Cell // D.geom.cellPatch C = i}, D.fresh.Pool C.1))
          ⟨patchPoolEquiv D D.l16_valid.pools_nonempty.choose i, Finset.mem_univ _⟩)).E
        (fun P => f ((patchPoolEquiv D).symm P)) := by
  classical
  let all (i : Fin PT.tiling.m) := (Finset.univ :
    Finset (∀ C : {C : D.geom.Cell // D.geom.cellPatch C = i}, D.fresh.Pool C.1))
  have hAll (i : Fin PT.tiling.m) : (all i).Nonempty :=
    ⟨patchPoolEquiv D D.l16_valid.pools_nonempty.choose i, Finset.mem_univ _⟩
  have he := uniform_expect_equiv (patchPoolEquiv D) Finset.univ
    (show (Finset.univ : Finset (∀ C, D.fresh.Pool C)).Nonempty from
      ⟨D.encoding.pools_nonempty.choose, Finset.mem_univ _⟩) f
  have hU := uniform_pi_sets all hAll
  have hi : (Finset.univ : Finset (∀ C, D.fresh.Pool C)).image (patchPoolEquiv D) = Finset.univ := by
    ext P
    simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact ⟨(patchPoolEquiv D).symm P, (patchPoolEquiv D).apply_symm_apply P⟩
  change (FinLaw.uniform Finset.univ ⟨D.encoding.pools_nonempty.choose, Finset.mem_univ _⟩).E f = _
  rw [he]
  have hImage : ((Finset.univ : Finset (∀ C, D.fresh.Pool C)).image (patchPoolEquiv D)).Nonempty :=
    (show (Finset.univ : Finset (∀ C, D.fresh.Pool C)).Nonempty from
      ⟨D.encoding.pools_nonempty.choose, Finset.mem_univ _⟩).image (patchPoolEquiv D)
  have hLaw : FinLaw.uniform (Finset.univ.image (patchPoolEquiv D)) hImage =
      FinLaw.pi (fun i => FinLaw.uniform (all i) (hAll i)) := by
    rw [← hU]
    congr 1
    ext P
    simp only [hi, Finset.mem_filter, Finset.mem_univ, true_and, all]
    constructor
    · intro _ i
      trivial
    · intro _
      trivial
  rw [hLaw]

theorem pi_expect_coord {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i))
    (i : ι) (f : Ω i → ℝ) : (FinLaw.pi P).E (fun x => f (x i)) = (P i).E f := by
  classical
  let g : ∀ j, Ω j → ℝ := fun j x => if hj : j = i then f (cast (congrArg Ω hj) x) else 1
  have hprod (x : ∀ j, Ω j) : (∏ j, g j (x j)) = f (x i) := by
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro j _ hji
      simp [g, hji]
    · simp
  have hE (j : ι) (hj : j ≠ i) : (P j).E (g j) = 1 := by
    simp only [g, dif_neg hj]
    exact E_const _ 1
  have h := S16.Lane_q_s16_comp2.pi_expect_prod P g
  simp only [hprod] at h
  rw [Finset.prod_eq_single i] at h
  · simpa only [g, dif_pos rfl, cast_eq, dite_true] using h
  · intro j _ hji
    exact hE j hji
  · simp

private theorem pi_expect_cons {n : ℕ} {Ω : Fin (n + 1) → Type*}
    [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i)) (f : (∀ i, Ω i) → ℝ) :
    (FinLaw.pi P).E f = (FinLaw.pi (fun i : Fin n => P i.succ)).E
      (fun x => (P 0).E (fun a => f (Fin.cons a x))) := by
  simpa only [FinLaw.E, FinLaw.pi, HypercubeRamsey.Lane_q_s16_comp1.finiteExpectation,
    HypercubeRamsey.Lane_q_s16_comp1.dependentProductMass] using
    HypercubeRamsey.Lane_q_s16_comp1.dependentProductExpectation_cons (fun i => (P i).w) f

theorem pi_expect_local_dominate {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)]
    (P Q : ∀ i, FinLaw (Ω i)) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (R : ∀ i, Ω i → Ω i → Prop) (hR : ∀ i x, R i x x)
    (hcomp : ∀ i, ∀ g : Ω i → ℝ, (∀ x, 0 ≤ g x) →
      (∀ x y, R i x y → g x = g y) → (P i).E g ≤ c i * (Q i).E g)
    (f : (∀ i, Ω i) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hlocal : ∀ x y, (∀ i, R i (x i) (y i)) → f x = f y) :
    (FinLaw.pi P).E f ≤ (∏ i, c i) * (FinLaw.pi Q).E f := by
  classical
  induction n with
  | zero => simp [FinLaw.E, FinLaw.pi]
  | succ n ih =>
      let g := fun x : ∀ i : Fin n, Ω i.succ => (Q 0).E (fun a => f (Fin.cons a x))
      have hg : ∀ x, 0 ≤ g x := by
        intro x
        apply Finset.sum_nonneg
        intro a _
        exact mul_nonneg ((Q 0).nonneg a) (hf (Fin.cons a x))
      have hglocal : ∀ x y, (∀ i : Fin n, R i.succ (x i) (y i)) → g x = g y := by
        intro x y hxy
        change (Q 0).E (fun a => f (Fin.cons a x)) = (Q 0).E (fun a => f (Fin.cons a y))
        apply congrArg (Q 0).E
        funext a
        apply hlocal
        intro i
        refine Fin.cases ?_ ?_ i
        · exact hR 0 a
        · intro j
          exact hxy j
      have hhead (x : ∀ i : Fin n, Ω i.succ) :
          (P 0).E (fun a => f (Fin.cons a x)) ≤ c 0 * g x := by
        apply hcomp 0 _ (fun a => hf (Fin.cons a x))
        intro a b hab
        apply hlocal
        intro i
        refine Fin.cases ?_ ?_ i
        · exact hab
        · intro j
          exact hR j.succ (x j)
      rw [pi_expect_cons P f, pi_expect_cons Q f, Fin.prod_univ_succ]
      calc
        _ ≤ (FinLaw.pi (fun i : Fin n => P i.succ)).E (fun x => c 0 * g x) :=
          S16.Lane_q_s16_comp2.expect_le _ _ _ hhead
        _ = c 0 * (FinLaw.pi (fun i : Fin n => P i.succ)).E g := by
          unfold FinLaw.E
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ ≤ c 0 * ((∏ i : Fin n, c i.succ) * (FinLaw.pi (fun i : Fin n => Q i.succ)).E g) :=
          mul_le_mul_of_nonneg_left
            (ih (fun i : Fin n => P i.succ) (fun i : Fin n => Q i.succ) (fun i : Fin n => c i.succ)
              (fun i => hc i.succ) (fun i : Fin n => R i.succ) (fun i => hR i.succ)
              (fun i => hcomp i.succ) g hg hglocal) (hc 0)
        _ = _ := by dsimp [g]; ring

noncomputable def scopedPatchSlots (D : LateData hPT) (region : Finset D.geom.Cell)
    (i : Fin PT.tiling.m) : Finset (S16.CellSlot D.geom) :=
  Finset.univ.filter fun s => s.1 ∈ region ∧ D.geom.cellPatch s.1 = i

theorem physical_poolComparison (D : LateData hPT) : S16.PoolComparison D.geom := by
  obtain ⟨p⟩ := D.l16_valid.physical
  have h : S16.PoolComparison p.geometry.geom := p.geometry.pool_comparison
  rw [p.geometry_eq] at h
  exact h

theorem scoped_pool_comparison (D : LateData hPT) (region : Finset D.geom.Cell)
    (hsize : ∀ i, ((scopedPatchSlots D region i).card : ℝ) ≤
      Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 10))
    (hroom : ∀ i, 2 * (((scopedPatchSlots D region i).card : ℝ) + 1) ^ 2 ≤
      Fintype.card (Bin PT.tiling i))
    (hcost : (∏ i : Fin PT.tiling.m,
      (1 + ((scopedPatchSlots D region i).card : ℝ) ^ 2 /
        Fintype.card (Bin PT.tiling i))) ≤ 2)
    (f : (∀ C, D.fresh.Pool C) → ℝ) (hf : ∀ P, 0 ≤ f P)
    (hlocal : ∀ P Q, (∀ C ∈ region, P C = Q C) → f P = f Q) :
    D.encoding.poolLaw.E f ≤ 2 * D.encoding.iidLaw.E f := by
  classical
  let Ω := fun i : Fin PT.tiling.m => ∀ C : {C : D.geom.Cell // D.geom.cellPatch C = i}, D.fresh.Pool C.1
  let P : ∀ i, FinLaw (Ω i) := fun i => FinLaw.uniform (patchPermPools D i) (patchPermPools_nonempty D i)
  let Q : ∀ i, FinLaw (Ω i) := fun i => FinLaw.uniform Finset.univ
    ⟨patchPoolEquiv D D.l16_valid.pools_nonempty.choose i, Finset.mem_univ _⟩
  let c := fun i : Fin PT.tiling.m => 1 + ((scopedPatchSlots D region i).card : ℝ) ^ 2 /
    Fintype.card (Bin PT.tiling i)
  let R := fun (i : Fin PT.tiling.m) (x y : Ω i) => ∀ C, C.1 ∈ region → x C = y C
  have hc : ∀ i, 0 ≤ c i := by intro i; dsimp [c]; positivity
  have hR : ∀ i x, R i x x := by intro i x C _; rfl
  have hcomp : ∀ i, ∀ g : Ω i → ℝ, (∀ x, 0 ≤ g x) →
      (∀ x y, R i x y → g x = g y) → (P i).E g ≤ c i * (Q i).E g := by
    intro i g hg hgLocal
    let F := fun pools : ∀ C, D.fresh.Pool C => g (patchPoolEquiv D pools i)
    have hF : ∀ pools, 0 ≤ F pools := fun pools => hg _
    have hdep : S16.DependsOnCellSlots (scopedPatchSlots D region i) F := by
      intro pools pools' hslots
      apply hgLocal
      intro C hC
      funext t
      exact hslots ⟨C.1, t⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC, C.2⟩)
    have hpatch : ∀ slot ∈ scopedPatchSlots D region i, D.geom.cellPatch slot.1 = i := by
      intro slot hslot
      exact (Finset.mem_filter.mp hslot).2.2
    have hPC := (physical_poolComparison D i D.encoding.pools_nonempty
      (scopedPatchSlots D region i) hpatch (hsize i) (hroom i) F hF hdep).1
    have hP : D.encoding.poolLaw.E F = (P i).E g := by
      rw [permPool_expect_patchwise]
      change (FinLaw.pi P).E (fun x => g (patchPoolEquiv D ((patchPoolEquiv D).symm x) i)) = _
      simp only [(patchPoolEquiv D).apply_symm_apply]
      exact pi_expect_coord P i g
    have hQ : D.encoding.iidLaw.E F = (Q i).E g := by
      rw [iidPool_expect_patchwise]
      change (FinLaw.pi Q).E (fun x => g (patchPoolEquiv D ((patchPoolEquiv D).symm x) i)) = _
      simp only [(patchPoolEquiv D).apply_symm_apply]
      exact pi_expect_coord Q i g
    change D.encoding.poolLaw.E F ≤ c i * D.encoding.iidLaw.E F at hPC
    rwa [hP, hQ] at hPC
  have htestLocal : ∀ x y, (∀ i, R i (x i) (y i)) →
      f ((patchPoolEquiv D).symm x) = f ((patchPoolEquiv D).symm y) := by
    intro x y hxy
    apply hlocal
    intro C hC
    exact hxy (D.geom.cellPatch C) ⟨C, rfl⟩ hC
  have h := pi_expect_local_dominate P Q c hc R hR hcomp
    (fun x => f ((patchPoolEquiv D).symm x)) (fun x => hf _) htestLocal
  have hP := permPool_expect_patchwise D f
  have hQ := iidPool_expect_patchwise D f
  change D.encoding.poolLaw.E f = (FinLaw.pi P).E (fun x => f ((patchPoolEquiv D).symm x)) at hP
  change D.encoding.iidLaw.E f = (FinLaw.pi Q).E (fun x => f ((patchPoolEquiv D).symm x)) at hQ
  rw [← hP, ← hQ] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right hcost
  apply Finset.sum_nonneg
  intro pools _
  exact mul_nonneg (D.encoding.iidLaw.nonneg pools) (hf pools)

end HypercubeRamsey.S18.Lane_sol_s18_n5
