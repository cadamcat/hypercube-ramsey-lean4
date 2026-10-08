import HypercubeRamsey.S05.History_sol_s05_1f

namespace HypercubeRamsey.Lane_sol_s05_1f

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

/-- The candidate normalizer gate bounds each actual block likelihood. -/
theorem candidate_block_likelihood (H : X.KeyHist) (K : X.Ty) (ℓ : X.Key)
    (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) (hℓ : ℓ ∈ K.2.1)
    (hd : 0 < X.blockMass H K (K.2.1.erase ℓ))
    (hr : Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) * colLen5 (X.p.s n) ℓ) *
      X.blockMass H K (K.2.1.erase ℓ) ≤ X.blockMass (X.withCol H ℓ θ) K K.2.1)
    (z : X.Block K) :
    ratio5 ((X.blockLaw (X.withCol H ℓ θ) K).w z) ((X.blockLawDel H K ℓ).w z) ≤
      Real.exp (X.p.a 2 * (X.p.q0 * X.p.typeSegs n K) * colLen5 (X.p.s n) ℓ) := by
  let L : ℝ := (X.p.q0 * X.p.typeSegs n K : ℕ)
  let s : ℝ := colLen5 (X.p.s n) ℓ
  let A := Real.exp (X.p.a 1 * L * s)
  let B := Real.exp (-(X.p.delta * L) * s)
  have hBne : B ≠ 0 := (Real.exp_pos _).ne'
  have hfull : 0 < X.blockMass (X.withCol H ℓ θ) K K.2.1 :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _) hd) hr
  have hn := Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg
    (X.blockWeight (X.withCol H ℓ θ) K K.2.1) (X.fallbackBlock K) z
    (Lane_q_s05_hist1b.blockWeight_nonneg X (X.withCol H ℓ θ) K K.2.1) hfull
  have hdn := Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg
    (X.blockWeight H K (K.2.1.erase ℓ)) (X.fallbackBlock K) z
    (Lane_q_s05_hist1b.blockWeight_nonneg X H K (K.2.1.erase ℓ)) hd
  have hweight : X.blockWeight (X.withCol H ℓ θ) K K.2.1 z ≤
      A * X.blockWeight H K (K.2.1.erase ℓ) z := by
    simpa [A, L, s, Nat.cast_mul] using
      Lane_q_s05_hist1b.blockWeight_withCol_le X H K ℓ z θ hℓ
  have hlaw : (X.blockLaw (X.withCol H ℓ θ) K).w z ≤
      (A / B) * (X.blockLawDel H K ℓ).w z := by
    change (normalize5 _ _).w z ≤ (A / B) * (normalize5 _ _).w z
    rw [hn, hdn]
    apply (div_le_iff₀ hfull).mpr
    have hbr : B * X.blockMass H K (K.2.1.erase ℓ) ≤
        X.blockMass (X.withCol H ℓ θ) K K.2.1 := by
      simpa only [B, L, s, Nat.cast_mul] using hr
    calc
      _ ≤ A * X.blockWeight H K (K.2.1.erase ℓ) z := hweight
      _ = ((A / B) * (X.blockWeight H K (K.2.1.erase ℓ) z /
          X.blockMass H K (K.2.1.erase ℓ))) *
          (B * X.blockMass H K (K.2.1.erase ℓ)) := by
        field_simp [hd.ne', hBne]
      _ ≤ _ := mul_le_mul_of_nonneg_left hbr (by
        exact mul_nonneg (div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          (div_nonneg (Lane_q_s05_hist1b.blockWeight_nonneg X H K _ z) hd.le))
  have hab : A / B ≤ Real.exp (X.p.a 2 * L * s) := by
    dsimp only [A, B]
    rw [← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    have hgap := X.p.hdelta_a (1 : Fin 9) (2 : Fin 9) (by decide)
    have ho := X.p.ha_order (1 : Fin 9) (2 : Fin 9) (by decide)
    have ha : X.p.a 1 + X.p.delta ≤ X.p.a 2 := by linarith
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ha (show 0 ≤ L by dsimp [L]; positivity))
      (show 0 ≤ s by dsimp [s]; positivity)
    nlinarith
  by_cases hz : (X.blockLawDel H K ℓ).w z = 0
  · simp only [ratio5, hz, ite_true]
    exact (Real.exp_pos _).le
  · have hpos := lt_of_le_of_ne ((X.blockLawDel H K ℓ).nonneg z) (Ne.symm hz)
    simp only [ratio5, hz, ite_false]
    simpa only [L, s, Nat.cast_mul] using ((div_le_iff₀ hpos).mpr hlaw).trans hab

/-- Indices removed from one array inject into the stored subset. -/
theorem inRef_card {Id : Type} [DecidableEq Id]
    (d : Id × X.Ty × Finset (Fin X.blockBound)) (c : Id × X.Ty) :
    (Finset.univ.filter fun i : Fin (X.p.typeBlocks n c.2) => X.InRef (some d) c i).card ≤
      d.2.2.card := by
  let S := Finset.univ.filter fun i : Fin (X.p.typeBlocks n c.2) => X.InRef (some d) c i
  have hj (i : {i // i ∈ S}) : ∃ j ∈ d.2.2, X.blockIdx c.2 j = some i.1 := by
    have hh := (Finset.mem_filter.mp i.2).2
    obtain ⟨e, he, hc, hj⟩ := hh
    cases Option.some.inj he
    exact hj
  let f (i : {i // i ∈ S}) : {j // j ∈ d.2.2} :=
    ⟨Classical.choose (hj i), (Classical.choose_spec (hj i)).1⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro i j he
  apply Subtype.ext
  have hi := (Classical.choose_spec (hj i)).2
  have hje := (Classical.choose_spec (hj j)).2
  have hval : (f i).1 = (f j).1 := congrArg Subtype.val he
  dsimp only [f] at hval
  rw [hval, hje] at hi
  exact (Option.some.inj hi).symm

private theorem removed_product_le {Id : Type} [DecidableEq Id]
    (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) (hg : X.candGateOn H r a θ)
    (d : Id × X.Ty × Finset (Fin X.blockBound)) (c : Id × X.Ty)
    (hc : c ∈ r.2.1.filter fun c => r.1 ∈ c.2.2.1) :
    (∏ i : Fin (X.p.typeBlocks n c.2), if X.InRef (some d) c i then
      ratio5 ((X.blockLaw (X.withCol H r.1 θ) c.2).w (a c i))
        ((X.blockLawDel H c.2 r.1).w (a c i)) else 1) ≤
      if c = (d.1, d.2.1) then
        Real.exp (X.p.a 2 * X.refLen d.2.1 d.2.2 * colLen5 (X.p.s n) r.1) else 1 := by
  by_cases he : c = (d.1, d.2.1)
  · rw [if_pos he]
    have hmem := (Finset.mem_filter.mp hc).2
    have hgate := hg.1 c (Finset.mem_filter.mp hc).1 hmem
    let B := Real.exp (X.p.a 2 * (X.p.q0 * X.p.typeSegs n c.2) * colLen5 (X.p.s n) r.1)
    let S := Finset.univ.filter fun i : Fin (X.p.typeBlocks n c.2) => X.InRef (some d) c i
    have hB : 1 ≤ B := by
      apply Real.one_le_exp_iff.mpr
      have ha : 0 < X.p.a 2 := by
        have hh := X.p.ha_order (0 : Fin 9) (2 : Fin 9) (by decide)
        rw [X.p.ha0] at hh
        linarith
      exact mul_nonneg (mul_nonneg ha.le (by positivity)) (by positivity)
    rw [← Finset.prod_filter]
    calc
      _ ≤ B ^ S.card := by
        have hp := Finset.prod_le_prod₀ (s := S)
          (f := fun i => ratio5 ((X.blockLaw (X.withCol H r.1 θ) c.2).w (a c i))
            ((X.blockLawDel H c.2 r.1).w (a c i))) (g := fun _ => B)
          (fun i _ => Lane_q_s05_hist1b.ratio5_nonneg
            ((X.blockLaw (X.withCol H r.1 θ) c.2).nonneg _) ((X.blockLawDel H c.2 r.1).nonneg _))
          (fun i _ => candidate_block_likelihood X H c.2 r.1 θ hmem hgate.1 hgate.2 (a c i))
        simpa using hp
      _ ≤ B ^ d.2.2.card := pow_le_pow_right₀ hB (inRef_card X d c)
      _ = _ := by
        dsimp [B]
        rw [← Real.exp_nat_mul]
        simp only [Setup5.refLen, Nat.cast_mul, he]
        ring_nf
  · rw [if_neg he]
    have hn (i : Fin (X.p.typeBlocks n c.2)) : ¬ X.InRef (some d) c i := by
      rintro ⟨e, he', hc', _⟩
      cases Option.some.inj he'
      exact he hc'
    simp [hn]

/-- Removing a subset from a single array loses at most its block likelihood budget. -/
theorem obsLikOn_delete_domination {Id : Type} [DecidableEq Id]
    (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) (hg : X.candGateOn H r a θ)
    (d : Id × X.Ty × Finset (Fin X.blockBound)) :
    X.obsLikOn H r a θ none ≤
      Real.exp (X.p.a 2 * X.refLen d.2.1 d.2.2 * colLen5 (X.p.s n) r.1) *
        X.obsLikOn H r a θ (some d) := by
  classical
  letI : DecidableEq (Id × X.Ty) := Classical.decEq _
  let S := r.2.1.filter fun c => r.1 ∈ c.2.2.1
  let f := fun (c : Id × X.Ty) (i : Fin (X.p.typeBlocks n c.2)) =>
    ratio5 ((X.blockLaw (X.withCol H r.1 θ) c.2).w (a c i))
      ((X.blockLawDel H c.2 r.1).w (a c i))
  let removed := fun c => ∏ i : Fin (X.p.typeBlocks n c.2),
    if X.InRef (some d) c i then f c i else 1
  let B := Real.exp (X.p.a 2 * X.refLen d.2.1 d.2.2 * colLen5 (X.p.s n) r.1)
  have hremoved : (∏ c ∈ S, removed c) ≤ B := by
    have hm : (∏ c ∈ S, removed c) ≤ ∏ c ∈ S, if c = (d.1, d.2.1) then B else 1 :=
      Finset.prod_le_prod₀ (fun c _ => Finset.prod_nonneg fun i _ => by
        change 0 ≤ if X.InRef (some d) c i then f c i else 1
        split_ifs
        · exact Lane_q_s05_hist1b.ratio5_nonneg
            ((X.blockLaw (X.withCol H r.1 θ) c.2).nonneg _) ((X.blockLawDel H c.2 r.1).nonneg _)
        · norm_num)
        (fun c hc => by
          have hb := removed_product_le X H r a θ hg d c hc
          by_cases he : c = (d.1, d.2.1)
          · simpa only [removed, f, B, if_pos he] using hb
          · simpa only [removed, f, B, if_neg he] using hb)
    calc
      _ ≤ ∏ c ∈ S, if c = (d.1, d.2.1) then B else 1 := hm
      _ = if (d.1, d.2.1) ∈ S then B else 1 :=
        Finset.prod_ite_eq' S (d.1, d.2.1) (fun _ => B)
      _ ≤ B := by
        split_ifs
        · exact le_rfl
        · apply Real.one_le_exp_iff.mpr
          have ha : 0 < X.p.a 2 := by
            have hh := X.p.ha_order (0 : Fin 9) (2 : Fin 9) (by decide)
            rw [X.p.ha0] at hh; linarith
          exact mul_nonneg (mul_nonneg ha.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have heq : X.obsLikOn H r a θ none =
      X.obsLikOn H r a θ (some d) * ∏ c ∈ S, removed c := by
    unfold Setup5.obsLikOn
    simp only [Setup5.InRef, reduceCtorEq, false_and, exists_false, ite_false]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro c hc
    dsimp only [removed]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    change f c i = (if X.InRef (some d) c i then 1 else f c i) *
      (if X.InRef (some d) c i then f c i else 1)
    split_ifs <;> simp
  rw [heq, mul_comm B]
  exact mul_le_mul_of_nonneg_left hremoved
    (Lane_sol_s05_hist1b.obsLikOn_nonneg X H r a θ (some d))

/-- A positive Step 3 integrand defines a finite posterior law. -/
def posteriorLaw {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (excl : Option (Id × X.Ty × Finset (Fin X.blockBound)))
    (hpos : 0 < X.step3MassOn H r a excl) :
    FinProb (Fin (colLen5 (X.p.s n) r.1) → Fin N) where
  w := X.step3PostOn H r a excl
  nonneg θ := by
    apply div_nonneg _ hpos.le
    apply mul_nonneg _ (Lane_sol_s05_hist1b.obsLikOn_nonneg X H r a θ excl)
    apply mul_nonneg (Finset.prod_nonneg fun h _ => (X.prior H.1 r.1).nonneg _)
    split_ifs <;> norm_num
  sum_eq_one := by
    unfold Setup5.step3PostOn
    rw [← Finset.sum_div]
    change X.step3MassOn H r a excl / X.step3MassOn H r a excl = 1
    exact div_self hpos.ne'

/-- The passing ratio test converts the likelihood budget into the concrete
full/deleted posterior domination, with the paper's a₃ slack. -/
theorem posterior_delete_domination {Id : Type} [DecidableEq Id]
    (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (d : Id × X.Ty × Finset (Fin X.blockBound))
    (hp : 0 < X.step3MassOn H r a none) (hq : 0 < X.step3MassOn H r a (some d))
    (hr : Real.exp (-(X.p.delta * X.refLen d.2.1 d.2.2 * colLen5 (X.p.s n) r.1)) *
      X.step3MassOn H r a (some d) ≤ X.step3MassOn H r a none)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.step3PostOn H r a none θ ≤
      Real.exp (X.p.a 3 * X.refLen d.2.1 d.2.2 * colLen5 (X.p.s n) r.1) *
        X.step3PostOn H r a (some d) θ := by
  by_cases hg : X.candGateOn H r a θ
  · let k : ℝ := X.refLen d.2.1 d.2.2
    let s : ℝ := colLen5 (X.p.s n) r.1
    let A := Real.exp (X.p.a 2 * k * s)
    let B := Real.exp (-(X.p.delta * k * s))
    have hBne : B ≠ 0 := (Real.exp_pos _).ne'
    let w := (∏ h, (X.prior H.1 r.1).w (θ h))
    have hw : 0 ≤ w := Finset.prod_nonneg fun h _ => (X.prior H.1 r.1).nonneg _
    have hlik := obsLikOn_delete_domination X H r a θ hg d
    have hnum : w * X.obsLikOn H r a θ none ≤ A * (w * X.obsLikOn H r a θ (some d)) := by
      have hh := mul_le_mul_of_nonneg_left hlik hw
      simpa [A, k, s, mul_left_comm] using hh
    have hAB : A / B ≤ Real.exp (X.p.a 3 * k * s) := by
      dsimp only [A, B]
      rw [← Real.exp_sub]
      apply Real.exp_le_exp.mpr
      have hgap := X.p.hdelta_a (2 : Fin 9) (3 : Fin 9) (by decide)
      have ho := X.p.ha_order (2 : Fin 9) (3 : Fin 9) (by decide)
      have ha : X.p.a 2 + X.p.delta ≤ X.p.a 3 := by linarith
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ha (show 0 ≤ k by exact Nat.cast_nonneg _))
        (show 0 ≤ s by exact Nat.cast_nonneg _)
      nlinarith
    unfold Setup5.step3PostOn
    simp only [if_pos hg, mul_one]
    change w * _ / _ ≤ _ * (w * _ / _)
    calc
      _ ≤ (A / B) * (w * X.obsLikOn H r a θ (some d) /
          X.step3MassOn H r a (some d)) := by
        apply (div_le_iff₀ hp).mpr
        calc
          _ ≤ A * (w * X.obsLikOn H r a θ (some d)) := hnum
          _ = ((A / B) * (w * X.obsLikOn H r a θ (some d) /
              X.step3MassOn H r a (some d))) *
              (B * X.step3MassOn H r a (some d)) := by
            field_simp [hq.ne', hBne]
          _ ≤ _ := mul_le_mul_of_nonneg_left hr (by
            exact mul_nonneg (div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
              (div_nonneg (mul_nonneg hw (Lane_sol_s05_hist1b.obsLikOn_nonneg X H r a θ _)) hq.le))
      _ ≤ _ := mul_le_mul_of_nonneg_right hAB
        (div_nonneg (mul_nonneg hw (Lane_sol_s05_hist1b.obsLikOn_nonneg X H r a θ _)) hq.le)
  · simp [Setup5.step3PostOn, hg]


/-- The likelihood comparison also controls the two normalizing masses. -/
theorem step3Mass_delete_domination {Id : Type} [DecidableEq Id]
    (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (d : Id × X.Ty × Finset (Fin X.blockBound)) :
    X.step3MassOn H r a none ≤
      Real.exp (X.p.a 2 * X.refLen d.2.1 d.2.2 * colLen5 (X.p.s n) r.1) *
        X.step3MassOn H r a (some d) := by
  unfold Setup5.step3MassOn
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro θ _
  by_cases hg : X.candGateOn H r a θ
  · simp only [if_pos hg, mul_one]
    have hw : 0 ≤ ∏ h : Fin (colLen5 (X.p.s n) r.1), (X.prior H.1 r.1).w (θ h) :=
      Finset.prod_nonneg fun h _ => (X.prior H.1 r.1).nonneg (θ h)
    have hh := mul_le_mul_of_nonneg_left (obsLikOn_delete_domination X H r a θ hg d) hw
    simpa only [mul_left_comm] using hh
  · simp [hg]

theorem step3Mass_deleted_pos {Id : Type} [DecidableEq Id]
    (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (d : Id × X.Ty × Finset (Fin X.blockBound)) (hp : 0 < X.step3MassOn H r a none) :
    0 < X.step3MassOn H r a (some d) := by
  have hh := hp.trans_le (step3Mass_delete_domination X H r a d)
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hh

theorem step3PostOn_withCol {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id)
    (a : X.ArraysOn Id) (θ θ' : Fin (colLen5 (X.p.s n) r.1) → Fin N)
    (excl : Option (Id × X.Ty × Finset (Fin X.blockBound))) :
    X.step3PostOn (X.withCol H r.1 θ') r a excl θ = X.step3PostOn H r a excl θ := by
  simp only [Setup5.step3PostOn, Lane_sol_s05_hist1b.candGateOn_withCol,
    Lane_sol_s05_hist1b.obsLikOn_withCol, Lane_sol_s05_hist1b.step3MassOn_withCol]
  rfl

/-- High subset extraction only consults optional low columns, so replacing
its high target cannot change a computed reference. -/
theorem refsOn_withCol_high {Id : Type} [DecidableEq Id]
    (H : X.KeyHist) (r : X.RecordOn Id) (hh : r.1.isRight) (a : X.ArraysOn Id)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.refsOn (X.withCol H r.1 θ) r a = X.refsOn H r a := by
  unfold Setup5.refsOn
  apply Finset.image_congr
  intro c hc
  change (c.1, c.2.1, X.refSubsetOn (X.withCol H r.1 θ) a (c.1, c.2.1) c.2.2) =
    (c.1, c.2.1, X.refSubsetOn H a (c.1, c.2.1) c.2.2)
  suffices he : X.refSubsetOn (X.withCol H r.1 θ) a (c.1, c.2.1) c.2.2 =
      X.refSubsetOn H a (c.1, c.2.1) c.2.2 by rw [he]
  unfold Setup5.refSubsetOn
  dsimp only
  split
  · rfl
  · cases ho : c.2.2 with
    | none => rfl
    | some ℓ =>
      cases ℓ with
      | inr q => rfl
      | inl k =>
        have hne : (.inl k : X.Key) ≠ r.1 := by
          cases h : r.1 <;> simp_all
        simp only [Setup5.lowCol, Setup5.withCol, Function.update_of_ne hne]
        rfl

theorem high_record_mask_none (r : X.AbsRecord) (hr : X.RecOccurs r) (hh : r.1.isRight) :
    r.2.2.2 = none := by
  obtain ⟨y, μ, hrec⟩ := hr
  cases hm : r.2.2.2 with
  | none => rfl
  | some d =>
    have hleft := hrec.2.2.2
    rw [hm] at hleft
    have hl := hleft.1
    cases h : r.1 <;> simp_all

end
end HypercubeRamsey.Lane_sol_s05_1f
