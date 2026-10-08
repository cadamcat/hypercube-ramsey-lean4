import HypercubeRamsey.Framework.FinProb

namespace HypercubeRamsey.Lane_sol_finner

open scoped BigOperators

private theorem expect_nonneg {α : Type*} [Fintype α] (P : FinProb α)
    {g : α → ℝ} (hg : ∀ x, 0 ≤ g x) : 0 ≤ P.expect g :=
  Finset.sum_nonneg fun x _ => mul_nonneg (P.nonneg x) (hg x)

private theorem expect_mono {α : Type*} [Fintype α] (P : FinProb α)
    {g h : α → ℝ} (hgh : ∀ x, g x ≤ h x) : P.expect g ≤ P.expect h :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hgh x) (P.nonneg x)

private theorem expect_const {α : Type*} [Fintype α] (P : FinProb α) (c : ℝ) :
    P.expect (fun _ => c) = c := by
  simp [FinProb.expect, ← Finset.sum_mul, P.sum_eq_one]

/-- Weighted finite Hölder, assigning unused exponent weight to the constant one. -/
theorem holder {α B : Type*} [Fintype α] (P : FinProb α) (T : Finset B)
    (d : ℕ) (hd : 0 < d) (hT : T.card ≤ d) (u : B → α → ℝ)
    (hu : ∀ b ∈ T, ∀ x, 0 ≤ u b x) :
    P.expect (fun x => ∏ b ∈ T, Real.rpow (u b x) ((d : ℝ)⁻¹)) ≤
      ∏ b ∈ T, Real.rpow (P.expect (u b)) ((d : ℝ)⁻¹) := by
  classical
  let p : ℝ := (d : ℝ)⁻¹
  let M : B → ℝ := fun b => P.expect (u b)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hp : 0 < p := inv_pos.mpr hdR
  have hMnonneg : ∀ b ∈ T, 0 ≤ M b := fun b hb => expect_nonneg P (hu b hb)
  have hTp : (T.card : ℝ) * p ≤ 1 := by
    dsimp [p]
    exact (mul_inv_le_iff₀ hdR).mpr (by simpa only [one_mul] using (show (T.card : ℝ) ≤ d by exact_mod_cast hT))
  by_cases hM : ∀ b ∈ T, 0 < M b
  · let g : B → α → ℝ := fun b x => u b x / M b
    have hg : ∀ b ∈ T, ∀ x, 0 ≤ g b x :=
      fun b hb x => div_nonneg (hu b hb x) (hMnonneg b hb)
    have hgsum : ∀ b ∈ T, P.expect (g b) = 1 := by
      intro b hb
      change (∑ x, P.w x * (u b x / M b)) = 1
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div]
      exact div_self (hM b hb).ne'
    have hmean : ∀ x, (∏ b ∈ T, Real.rpow (g b x) p) ≤
        (1 - (T.card : ℝ) * p) + ∑ b ∈ T, p * g b x := by
      intro x
      let w : Option T → ℝ := fun b => Option.casesOn b (1 - (T.card : ℝ) * p) (fun _ => p)
      let z : Option T → ℝ := fun b => Option.casesOn b 1 (fun b => g b x)
      have hw : ∀ b ∈ (Finset.univ : Finset (Option T)), 0 ≤ w b := by
        intro b _
        cases b with
        | none => exact sub_nonneg.mpr hTp
        | some b => exact hp.le
      have hw' : ∑ b, w b = 1 := by
        simp [w, Fintype.sum_option, Finset.sum_const, nsmul_eq_mul]
      have hz : ∀ b ∈ (Finset.univ : Finset (Option T)), 0 ≤ z b := by
        intro b _
        cases b with
        | none => exact zero_le_one
        | some b => exact hg b b.property x
      have hm := Real.geom_mean_le_arith_mean_weighted Finset.univ w z hw hw' hz
      simp only [w, z, Fintype.prod_option, Fintype.sum_option, Real.one_rpow,
        one_mul, mul_one] at hm
      change (∏ b : T, (g b x) ^ p) ≤
        (1 - (T.card : ℝ) * p) + ∑ b : T, p * g b x at hm
      rw [Finset.prod_coe_sort T (fun b => (g b x) ^ p),
        Finset.sum_coe_sort T (fun b => p * g b x)] at hm
      exact hm
    have hsum : P.expect (fun x => ∏ b ∈ T, Real.rpow (g b x) p) ≤ 1 := by
      calc
        _ ≤ P.expect (fun x => (1 - (T.card : ℝ) * p) + ∑ b ∈ T, p * g b x) :=
          expect_mono P hmean
        _ = (1 - (T.card : ℝ) * p) + ∑ b ∈ T, p * P.expect (g b) := by
          simp only [FinProb.expect, mul_add, Finset.sum_add_distrib]
          rw [← Finset.sum_mul, P.sum_eq_one, one_mul]
          congr 1
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = 1 := by
          rw [Finset.sum_congr rfl (fun b hb => by rw [hgsum b hb, mul_one])]
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
    have hprod : ∀ x, (∏ b ∈ T, Real.rpow (u b x) p) =
        (∏ b ∈ T, Real.rpow (M b) p) * (∏ b ∈ T, Real.rpow (g b x) p) := by
      intro x
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro b hb
      dsimp [g]
      rw [Real.div_rpow (hu b hb x) (hMnonneg b hb)]
      exact (mul_div_cancel₀ _ (Real.rpow_pos_of_pos (hM b hb) p).ne').symm
    change P.expect (fun x => ∏ b ∈ T, Real.rpow (u b x) p) ≤ ∏ b ∈ T, Real.rpow (M b) p
    calc
      _ = (∏ b ∈ T, Real.rpow (M b) p) *
          P.expect (fun x => ∏ b ∈ T, Real.rpow (g b x) p) := by
        simp only [FinProb.expect, hprod, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ ≤ (∏ b ∈ T, Real.rpow (M b) p) * 1 :=
        mul_le_mul_of_nonneg_left hsum (Finset.prod_nonneg fun b hb => Real.rpow_nonneg (hMnonneg b hb) p)
      _ = _ := mul_one _
  · push Not at hM
    obtain ⟨b, hb, hMb⟩ := hM
    have hzero : M b = 0 := le_antisymm hMb (hMnonneg b hb)
    have hrow : ∀ x, P.w x * u b x = 0 := by
      intro x
      apply le_antisymm _ (mul_nonneg (P.nonneg x) (hu b hb x))
      calc
        P.w x * u b x ≤ P.expect (u b) :=
          Finset.single_le_sum (fun y _ => mul_nonneg (P.nonneg y) (hu b hb y)) (Finset.mem_univ x)
        _ = 0 := hzero
    have hleft : P.expect (fun x => ∏ j ∈ T, Real.rpow (u j x) p) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      change P.w x * (∏ j ∈ T, Real.rpow (u j x) p) = 0
      rcases mul_eq_zero.mp (hrow x) with hw | hu0
      · rw [hw, zero_mul]
      · have hz : Real.rpow (u b x) p = 0 := by
          rw [hu0]
          exact Real.zero_rpow hp.ne'
        rw [Finset.prod_eq_zero hb hz, mul_zero]
    change P.expect (fun x => ∏ b ∈ T, Real.rpow (u b x) p) ≤ ∏ b ∈ T, Real.rpow (M b) p
    rw [hleft]
    exact Finset.prod_nonneg fun j hj => Real.rpow_nonneg (hMnonneg j hj) p


section Coordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (Q : ∀ i, FinProb (Ω i))

noncomputable def avgOne (i : ι) (g : (∀ i, Ω i) → ℝ) (ω : ∀ i, Ω i) : ℝ :=
  (Q i).expect (fun x => g (Function.update ω i x))

noncomputable def avg : List ι → ((∀ i, Ω i) → ℝ) → (∀ i, Ω i) → ℝ
  | [], g => g
  | i :: L, g => avgOne Q i (avg L g)

omit [Fintype ι] in
private theorem avgOne_nonneg (i : ι) {g : (∀ i, Ω i) → ℝ} (hg : ∀ ω, 0 ≤ g ω) :
    ∀ ω, 0 ≤ avgOne Q i g ω := fun ω => expect_nonneg (Q i) (fun x => hg (Function.update ω i x))

omit [Fintype ι] in
private theorem avgOne_mono (i : ι) {g h : (∀ i, Ω i) → ℝ} (hgh : ∀ ω, g ω ≤ h ω) :
    ∀ ω, avgOne Q i g ω ≤ avgOne Q i h ω :=
  fun ω => expect_mono (Q i) (fun x => hgh (Function.update ω i x))

omit [Fintype ι] in
private theorem avgOne_scope (i : ι) {g : (∀ i, Ω i) → ℝ} {S : Finset ι}
    (hg : FinProb.DependsOn g S) : FinProb.DependsOn (avgOne Q i g) (S.erase i) := by
  intro ω ω' hω
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply hg
  intro j hj
  by_cases hji : j = i
  · subst j
    simp
  · simpa only [Function.update_of_ne hji] using hω j (Finset.mem_erase.mpr ⟨hji, hj⟩)

omit [Fintype ι] in
private theorem avgOne_comm (i j : ι) (g : (∀ i, Ω i) → ℝ) :
    avgOne Q i (avgOne Q j g) = avgOne Q j (avgOne Q i g) := by
  by_cases hij : i = j
  · subst j
    rfl
  · funext ω
    simp only [avgOne, FinProb.expect, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_comm hij]
    ring

private theorem avg_comm (i : ι) (L : List ι) (g : (∀ i, Ω i) → ℝ) :
    avgOne Q i (avg Q L g) = avg Q L (avgOne Q i g) := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    change avgOne Q i (avgOne Q j (avg Q L g)) = avgOne Q j (avg Q L (avgOne Q i g))
    rw [avgOne_comm, ih]

private theorem avg_mono (L : List ι) {g h : (∀ i, Ω i) → ℝ} (hgh : ∀ ω, g ω ≤ h ω) :
    ∀ ω, avg Q L g ω ≤ avg Q L h ω := by
  induction L with
  | nil => exact hgh
  | cons i L ih => exact avgOne_mono Q i ih

private theorem avg_scope (L : List ι) {g : (∀ i, Ω i) → ℝ} {S : Finset ι}
    (hg : FinProb.DependsOn g S) : FinProb.DependsOn (avg Q L g) (S \ L.toFinset) := by
  induction L with
  | nil => simpa only [avg, List.toFinset_nil, Finset.sdiff_empty] using hg
  | cons i L ih =>
    have hs : S \ (i :: L).toFinset = (S \ L.toFinset).erase i := by
      ext j
      simp only [List.toFinset_cons, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      tauto
    rw [hs]
    exact avgOne_scope Q i ih

private theorem expect_split (i : ι) (g : (∀ i, Ω i) → ℝ) :
    (FinProb.pi Q).expect g =
      (Q i).expect (fun x =>
        (FinProb.pi (fun j : {j : ι // j ≠ i} => Q j)).expect
          (fun η => g ((Equiv.piSplitAt i Ω).symm (x, η)))) := by
  classical
  let e := Equiv.piSplitAt i Ω
  change (∑ ω, (∏ j, (Q j).w (ω j)) * g ω) = _
  rw [← e.symm.sum_comp (fun ω => (∏ j, (Q j).w (ω j)) * g ω)]
  rw [Fintype.sum_prod_type]
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η hη
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have he : e.symm (x, η) i = x := by simp [e]
  have hej : ∀ j : {j : ι // j ≠ i}, e.symm (x, η) j = η j := by
    intro j
    simp [e, j.property]
  simp only [he, hej, FinProb.pi]
  ring

private theorem expect_avgOne (i : ι) (g : (∀ i, Ω i) → ℝ) :
    (FinProb.pi Q).expect (avgOne Q i g) = (FinProb.pi Q).expect g := by
  classical
  have hupdate : ∀ x (η : ∀ j : {j : ι // j ≠ i}, Ω j) y,
      Function.update ((Equiv.piSplitAt i Ω).symm (x, η)) i y =
        (Equiv.piSplitAt i Ω).symm (y, η) := by
    intro x η y
    apply (Equiv.piSplitAt i Ω).injective
    ext j
    · simp
    · simp [Equiv.piSplitAt, j.property]
  rw [expect_split Q i (avgOne Q i g), expect_split Q i g]
  have hswap : ∀ x,
      (FinProb.pi (fun j : {j : ι // j ≠ i} => Q j)).expect
        (fun η => avgOne Q i g ((Equiv.piSplitAt i Ω).symm (x, η))) =
      (Q i).expect (fun y =>
        (FinProb.pi (fun j : {j : ι // j ≠ i} => Q j)).expect
          (fun η => g ((Equiv.piSplitAt i Ω).symm (y, η)))) := by
    intro x
    simp only [FinProb.expect, avgOne, hupdate, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro η hη
    ring
  simp_rw [hswap]
  exact expect_const (Q i) _

private theorem expect_avg (L : List ι) (g : (∀ i, Ω i) → ℝ) :
    (FinProb.pi Q).expect (avg Q L g) = (FinProb.pi Q).expect g := by
  induction L with
  | nil => rfl
  | cons i L ih => exact (expect_avgOne Q i (avg Q L g)).trans ih

private theorem avg_all (g : (∀ i, Ω i) → ℝ) (ω : ∀ i, Ω i) :
    avg Q Finset.univ.toList g ω = (FinProb.pi Q).expect g := by
  have hscope : FinProb.DependsOn g Finset.univ := by
    intro η η' h
    exact congrArg g (funext fun i => h i (Finset.mem_univ i))
  have hc := avg_scope Q Finset.univ.toList hscope
  have hconst : avg Q Finset.univ.toList g = fun _ => avg Q Finset.univ.toList g ω := by
    funext η
    apply hc
    simp
  calc
    _ = (FinProb.pi Q).expect (avg Q Finset.univ.toList g) := by
      rw [hconst, expect_const]
    _ = _ := expect_avg Q _ g

private theorem one_step {B : Type*} [Fintype B] [DecidableEq B]
    (S : B → Finset ι) (d : ℕ) (hd : 0 < d)
    (hdegree : ∀ i, (Finset.univ.filter (fun b => i ∈ S b)).card ≤ d)
    (f : B → (∀ i, Ω i) → ℝ) (hnonneg : ∀ b ω, 0 ≤ f b ω)
    (hscope : ∀ b, FinProb.DependsOn (f b) (S b)) (i : ι) (ω : ∀ i, Ω i) :
    avgOne Q i (fun η => ∏ b, f b η) ω ≤
      ∏ b, (avgOne Q i (fun η => f b η ^ d) ω) ^ ((d : ℝ)⁻¹) := by
  classical
  let T := Finset.univ.filter (fun b => i ∈ S b)
  let U := Finset.univ.filter (fun b => i ∉ S b)
  let C := ∏ b ∈ U, f b ω
  let r : B → ℝ := fun b => (avgOne Q i (fun η => f b η ^ d) ω) ^ ((d : ℝ)⁻¹)
  have hconst : ∀ b ∈ U, ∀ x, f b (Function.update ω i x) = f b ω := by
    intro b hb x
    apply hscope b
    intro j hj
    have hni : i ∉ S b := (Finset.mem_filter.mp hb).2
    have hji : j ≠ i := fun h => hni (h ▸ hj)
    exact Function.update_of_ne hji x ω
  have hr : ∀ b ∈ U, r b = f b ω := by
    intro b hb
    dsimp [r, avgOne]
    simp_rw [hconst b hb]
    rw [expect_const]
    exact Real.pow_rpow_inv_natCast (hnonneg b ω) hd.ne'
  have hh := holder (Q i) T d hd (hdegree i)
    (fun b x => f b (Function.update ω i x) ^ d)
    (fun b hb x => pow_nonneg (hnonneg b _) d)
  have hh' : (Q i).expect (fun x => ∏ b ∈ T, f b (Function.update ω i x)) ≤ ∏ b ∈ T, r b := by
    convert hh using 1
    · congr 1
      funext x
      apply Finset.prod_congr rfl
      intro b hb
      exact (Real.pow_rpow_inv_natCast (hnonneg b _) hd.ne').symm
    · rfl
  have hsplit : ∀ x, (∏ b, f b (Function.update ω i x)) =
      (∏ b ∈ T, f b (Function.update ω i x)) * C := by
    intro x
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun b => i ∈ S b)]
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    exact hconst b hb x
  calc
    _ = (Q i).expect (fun x => (∏ b ∈ T, f b (Function.update ω i x)) * C) := by
      change (Q i).expect _ = (Q i).expect _
      congr 1
      exact funext hsplit
    _ = (Q i).expect (fun x => ∏ b ∈ T, f b (Function.update ω i x)) * C := by
      simp only [FinProb.expect, ← mul_assoc, ← Finset.sum_mul]
    _ ≤ (∏ b ∈ T, r b) * C :=
      mul_le_mul_of_nonneg_right hh' (Finset.prod_nonneg fun b hb => hnonneg b ω)
    _ = ∏ b, r b := by
      change (∏ b ∈ T, r b) * (∏ b ∈ U, f b ω) = ∏ b, r b
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun b => i ∈ S b) r]
      congr 1
      apply Finset.prod_congr rfl
      intro b hb
      exact (hr b hb).symm

/-- Tensorization of the one-coordinate inequality over any finite coordinate list. -/
theorem tensorize {B : Type*} [Fintype B] [DecidableEq B]
    (L : List ι) (S : B → Finset ι) (d : ℕ) (hd : 0 < d)
    (hdegree : ∀ i, (Finset.univ.filter (fun b => i ∈ S b)).card ≤ d)
    (f : B → (∀ i, Ω i) → ℝ) (hnonneg : ∀ b ω, 0 ≤ f b ω)
    (hscope : ∀ b, FinProb.DependsOn (f b) (S b)) (ω : ∀ i, Ω i) :
    avg Q L (fun η => ∏ b, f b η) ω ≤
      ∏ b, (avg Q L (fun η => f b η ^ d) ω) ^ ((d : ℝ)⁻¹) := by
  induction L generalizing S f with
  | nil =>
    apply le_of_eq
    apply Finset.prod_congr rfl
    intro b hb
    exact (Real.pow_rpow_inv_natCast (hnonneg b ω) hd.ne').symm
  | cons i L ih =>
    let g : B → (∀ i, Ω i) → ℝ :=
      fun b η => (avgOne Q i (fun η => f b η ^ d) η) ^ ((d : ℝ)⁻¹)
    have hg0 : ∀ b η, 0 ≤ g b η := fun b η =>
      Real.rpow_nonneg (avgOne_nonneg Q i (fun η => pow_nonneg (hnonneg b η) d) η) _
    have hgs : ∀ b, FinProb.DependsOn (g b) ((S b).erase i) := by
      intro b η η' hη
      apply congrArg (fun z : ℝ => z ^ ((d : ℝ)⁻¹))
      exact avgOne_scope Q i (fun η η' h => congrArg (fun z : ℝ => z ^ d) (hscope b η η' h)) η η' hη
    have hgdegree : ∀ j, (Finset.univ.filter (fun b => j ∈ (S b).erase i)).card ≤ d := by
      intro j
      apply le_trans (Finset.card_le_card ?_) (hdegree j)
      intro b hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, (Finset.mem_erase.mp (Finset.mem_filter.mp hb).2).2⟩
    have hgpow : ∀ b, (fun η => g b η ^ d) = avgOne Q i (fun η => f b η ^ d) := by
      intro b
      funext η
      exact Real.rpow_inv_natCast_pow
        (avgOne_nonneg Q i (fun η => pow_nonneg (hnonneg b η) d) η) hd.ne'
    calc
      _ = avg Q L (avgOne Q i (fun η => ∏ b, f b η)) ω := by
        exact congrFun (avg_comm Q i L (fun η => ∏ b, f b η)) ω
      _ ≤ avg Q L (fun η => ∏ b, g b η) ω :=
        avg_mono Q L (one_step Q S d hd hdegree f hnonneg hscope i) ω
      _ ≤ ∏ b, (avg Q L (fun η => g b η ^ d) ω) ^ ((d : ℝ)⁻¹) :=
        ih (fun b => (S b).erase i) hgdegree g hg0 hgs
      _ = _ := by
        apply Finset.prod_congr rfl
        intro b hb
        rw [hgpow, ← avg_comm]
        rfl

/-- Finner's inequality for the finite product law. -/
theorem finner {B : Type*} [Fintype B] [DecidableEq B]
    (S : B → Finset ι) (d : ℕ) (hd : 0 < d)
    (hdegree : ∀ i, (Finset.univ.filter (fun b => i ∈ S b)).card ≤ d)
    (f : B → (∀ i, Ω i) → ℝ) (hnonneg : ∀ b ω, 0 ≤ f b ω)
    (hscope : ∀ b, FinProb.DependsOn (f b) (S b)) :
    (FinProb.pi Q).expect (fun ω => ∏ b, f b ω) ≤
      ∏ b, Real.rpow ((FinProb.pi Q).expect (fun ω => f b ω ^ d)) ((d : ℝ)⁻¹) := by
  classical
  have hn : Nonempty (∀ i, Ω i) := by
    by_contra h
    have : IsEmpty (∀ i, Ω i) := not_nonempty_iff.mp h
    have he := (FinProb.pi Q).sum_eq_one
    simp at he
  obtain ⟨ω⟩ := hn
  have h := tensorize Q Finset.univ.toList S d hd hdegree f hnonneg hscope ω
  simpa only [avg_all, Real.rpow_eq_pow] using h

end Coordinates

end HypercubeRamsey.Lane_sol_finner
