import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_cal_query

namespace HypercubeRamsey.S18.Lane_sol_d18l_cal
open Classical
open scoped BigOperators
open S16.Lane_q_s16_comp2
set_option backward.isDefEq.respectTransparency false

/-- Integrate the last coordinate before the earlier bin assignments. -/
theorem pi_E_snoc {B : Type*} [Fintype B] {n : ℕ}
    (P : Fin (n + 1) → FinLaw B) (f : (Fin (n + 1) → B) → ℝ) :
    (FinLaw.pi P).E f = (P (Fin.last n)).E (fun y =>
      (FinLaw.pi fun i : Fin n => P i.castSucc).E
        (fun xs => f (Fin.snoc xs y))) := by
  classical
  unfold FinLaw.E
  change (∑ xs, (∏ i, (P i).w (xs i)) * f xs) = _
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => B)) _ _
    (fun _ => rfl), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xs _
  change (∏ i, (P i).w ((Fin.snoc xs y : Fin (n + 1) → B) i)) * f (Fin.snoc xs y) =
    (P (Fin.last n)).w y * ((∏ i : Fin n, (P i.castSucc).w (xs i)) *
      f (Fin.snoc xs y))
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- An earlier-bin match costs at most the number of earlier candidates
times the atom cap. Candidates may themselves be repeated. -/
theorem earlier_bin_mass {B : Type*} [Fintype B] [DecidableEq B] {n : ℕ}
    (P : FinLaw B) (xs : Fin n → B) (δ : ℝ) (hcap : ∀ b, P.w b ≤ δ) :
    P.pr (fun y => ∃ i, y = xs i) ≤ n * δ := by
  calc
    _ ≤ ∑ i : Fin n, P.pr (fun y => y = xs i) := pr_exists_le_sum P _
    _ = ∑ i : Fin n, P.w (xs i) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold FinLaw.pr
      rw [Finset.sum_eq_single (xs i)]
      · simp
      · intro y _ hy; simp [hy]
      · simp
    _ ≤ ∑ _i : Fin n, δ := Finset.sum_le_sum (fun i _ => hcap (xs i))
    _ = n * δ := by simp

/-- Reverse summation of one removed consultation, retaining every
earlier bin and every nonnegative test that depends on those bins. -/
theorem reverse_repeat_step {B : Type*} [Fintype B] [DecidableEq B] {n : ℕ}
    (P : Fin (n + 1) → FinLaw B) (δ : ℝ)
    (hcap : ∀ b, (P (Fin.last n)).w b ≤ δ)
    (f : (Fin n → B) → ℝ) (hf : ∀ xs, 0 ≤ f xs) :
    (FinLaw.pi P).E (fun xs =>
      if ∃ i : Fin n, xs (Fin.last n) = xs i.castSucc then
        f (fun i => xs i.castSucc) else 0) ≤
      (n * δ) * (FinLaw.pi fun i : Fin n => P i.castSucc).E f := by
  classical
  rw [pi_E_snoc]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  rw [expect_indep_comm]
  calc
    _ ≤ (FinLaw.pi fun i : Fin n => P i.castSucc).E (fun xs => n * δ * f xs) := by
      apply expect_le
      intro xs
      have hmass := earlier_bin_mass (P (Fin.last n)) xs δ hcap
      calc
        (P (Fin.last n)).E (fun y => if ∃ i, y = xs i then f xs else 0) =
            (P (Fin.last n)).pr (fun y => ∃ i, y = xs i) * f xs := by
          unfold FinLaw.E FinLaw.pr
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : ∃ i, y = xs i <;> simp [hy]
        _ ≤ n * δ * f xs := mul_le_mul_of_nonneg_right hmass (hf xs)
    _ = _ := expect_const_mul _ _ _

def maskDrops : {n : ℕ} → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, J => maskDrops (fun i : Fin n => J i.castSucc) +
      if J (Fin.last n) then 1 else 0

/-- Kept targets are distinct and avoid the fixed later kept targets.
Removed targets must match an earlier bin. -/
noncomputable def repeatMaskWeight {B : Type*} [DecidableEq B] :
    {n : ℕ} → (Fin n → Bool) → (Fin n → B → ℝ) → Finset B → (Fin n → B) → ℝ
  | 0, _, _, _, _ => 1
  | n + 1, J, u, forbidden, xs =>
      if J (Fin.last n) then
        if ∃ i : Fin n, xs (Fin.last n) = xs i.castSucc then
          repeatMaskWeight (fun i : Fin n => J i.castSucc)
            (fun i : Fin n => u i.castSucc) forbidden (fun i => xs i.castSucc)
        else 0
      else if xs (Fin.last n) ∈ forbidden then 0
      else u (Fin.last n) (xs (Fin.last n)) *
        repeatMaskWeight (fun i : Fin n => J i.castSucc)
          (fun i : Fin n => u i.castSucc) (insert (xs (Fin.last n)) forbidden)
          (fun i => xs i.castSucc)

/-- The retained part after reverse summation, preserving distinctness. -/
noncomputable def keptMaskWeight {B : Type*} [DecidableEq B] :
    {n : ℕ} → (Fin n → Bool) → (Fin n → B → ℝ) → Finset B → (Fin n → B) → ℝ
  | 0, _, _, _, _ => 1
  | n + 1, J, u, forbidden, xs =>
      if J (Fin.last n) then
        keptMaskWeight (fun i : Fin n => J i.castSucc)
          (fun i : Fin n => u i.castSucc) forbidden (fun i => xs i.castSucc)
      else if xs (Fin.last n) ∈ forbidden then 0
      else u (Fin.last n) (xs (Fin.last n)) *
        keptMaskWeight (fun i : Fin n => J i.castSucc)
          (fun i : Fin n => u i.castSucc) (insert (xs (Fin.last n)) forbidden)
          (fun i => xs i.castSucc)

theorem repeatMaskWeight_nonneg {B : Type*} [DecidableEq B] {n : ℕ}
    (J : Fin n → Bool) (u : Fin n → B → ℝ) (hu : ∀ a b, 0 ≤ u a b)
    (forbidden : Finset B) (xs : Fin n → B) : 0 ≤ repeatMaskWeight J u forbidden xs := by
  induction n generalizing forbidden with
  | zero => exact zero_le_one
  | succ n ih =>
    simp only [repeatMaskWeight]
    split_ifs
    · exact ih _ _ (fun i b => hu i.castSucc b) _ _
    · exact le_rfl
    · exact le_rfl
    · exact mul_nonneg (hu _ _) (ih _ _ (fun i b => hu i.castSucc b) _ _)

theorem keptMaskWeight_nonneg {B : Type*} [DecidableEq B] {n : ℕ}
    (J : Fin n → Bool) (u : Fin n → B → ℝ) (hu : ∀ a b, 0 ≤ u a b)
    (forbidden : Finset B) (xs : Fin n → B) : 0 ≤ keptMaskWeight J u forbidden xs := by
  induction n generalizing forbidden with
  | zero => exact zero_le_one
  | succ n ih =>
    simp only [keptMaskWeight]
    split_ifs
    · exact ih _ _ (fun i b => hu i.castSucc b) _ _
    · exact le_rfl
    · exact mul_nonneg (hu _ _) (ih _ _ (fun i b => hu i.castSucc b) _ _)

theorem expect_nonneg {B : Type*} [Fintype B] (P : FinLaw B)
    (f : B → ℝ) (hf : ∀ b, 0 ≤ f b) : 0 ≤ P.E f :=
  Finset.sum_nonneg fun b _ => mul_nonneg (P.nonneg b) (hf b)

theorem expect_const {B : Type*} [Fintype B] (P : FinLaw B) (c : ℝ) :
    P.E (fun _ => c) = c := by
  simp only [FinLaw.E, ← Finset.sum_mul, P.sum_one, one_mul]

/-- Reverse summation pays one atom-cap allowance per removed query while
retaining distinctness for the later iid pool cancellation. -/
theorem reverse_masks {B : Type*} [Fintype B] [DecidableEq B]
    (q : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ (n : ℕ), n ≤ q → ∀ (P : Fin n → FinLaw B),
      (∀ a b, (P a).w b ≤ δ) →
      ∀ (J : Fin n → Bool) (u : Fin n → B → ℝ), (∀ a b, 0 ≤ u a b) →
      ∀ forbidden : Finset B,
        (FinLaw.pi P).E (repeatMaskWeight J u forbidden) ≤
          (q * δ) ^ maskDrops J * (FinLaw.pi P).E (keptMaskWeight J u forbidden) := by
  intro n
  induction n with
  | zero =>
    intro hn P hcap J u hu forbidden
    simp only [repeatMaskWeight, keptMaskWeight, maskDrops, pow_zero, one_mul,
      expect_const]
    exact le_rfl
  | succ n ih =>
    intro hn P hcap J u hu forbidden
    let P' := fun i : Fin n => P i.castSucc
    let J' := fun i : Fin n => J i.castSucc
    let u' := fun i : Fin n => u i.castSucc
    have hn' : n ≤ q := by omega
    have hc' : ∀ a b, (P' a).w b ≤ δ := fun a b => hcap a.castSucc b
    have hu' : ∀ a b, 0 ≤ u' a b := fun a b => hu a.castSucc b
    have hprefix (S : Finset B) := ih hn' P' hc' J' u' hu' S
    cases hj : J (Fin.last n) with
    | true =>
      have hkeep : (FinLaw.pi P).E (keptMaskWeight J u forbidden) =
          (FinLaw.pi P').E (keptMaskWeight J' u' forbidden) := by
        rw [pi_E_snoc]
        simp only [keptMaskWeight, hj, Bool.true_eq, if_true, Fin.snoc_castSucc]
        exact expect_const _ _
      have hstep : (FinLaw.pi P).E (repeatMaskWeight J u forbidden) ≤
          (n * δ) * (FinLaw.pi P').E (repeatMaskWeight J' u' forbidden) := by
        simpa only [repeatMaskWeight, hj, Bool.true_eq, if_true] using
          reverse_repeat_step P δ (hcap (Fin.last n))
            (repeatMaskWeight J' u' forbidden)
            (repeatMaskWeight_nonneg J' u' hu' forbidden)
      calc
        _ ≤ (n * δ) * (FinLaw.pi P').E (repeatMaskWeight J' u' forbidden) := hstep
        _ ≤ (q * δ) * ((q * δ) ^ maskDrops J' *
            (FinLaw.pi P').E (keptMaskWeight J' u' forbidden)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn') hδ
          · exact hprefix forbidden
          · exact expect_nonneg _ _ (repeatMaskWeight_nonneg J' u' hu' forbidden)
          · exact mul_nonneg (Nat.cast_nonneg _) hδ
        _ = _ := by
          rw [hkeep]
          simp only [maskDrops, hj, Bool.true_eq, if_true, pow_succ]
          ring
    | false =>
      rw [pi_E_snoc, pi_E_snoc]
      calc
        _ ≤ (P (Fin.last n)).E (fun y => (q * δ) ^ maskDrops J' *
            (FinLaw.pi P').E (fun xs => keptMaskWeight J u forbidden (Fin.snoc xs y))) := by
          apply expect_le
          intro y
          by_cases hy : y ∈ forbidden
          · simp only [repeatMaskWeight, keptMaskWeight, hj, Bool.false_eq_true,
              if_false, Fin.snoc_last, if_pos hy]
            simp [FinLaw.E]
          · simp only [repeatMaskWeight, keptMaskWeight, hj, Bool.false_eq_true,
              if_false, Fin.snoc_last, if_neg hy, Fin.snoc_castSucc]
            rw [expect_const_mul, expect_const_mul]
            have h := mul_le_mul_of_nonneg_left (hprefix (insert y forbidden)) (hu (Fin.last n) y)
            simpa only [mul_left_comm] using h
        _ = _ := by
          rw [expect_const_mul]
          simp only [maskDrops, hj, Bool.false_eq_true, if_false, add_zero]
          rfl

noncomputable def queryRepeatMask {B : Type*} [DecidableEq B] :
    {n : ℕ} → (Fin n → B) → (Fin n → Bool)
  | 0, _ => Fin.elim0
  | n + 1, xs => Fin.snoc (queryRepeatMask (fun i : Fin n => xs i.castSucc))
      (decide (∃ i : Fin n, xs (Fin.last n) = xs i.castSucc))

/-- The bounded tests remaining after discarding all later visits to a bin. -/
noncomputable def retainedQueryWeight {B : Type*} [DecidableEq B] :
    {n : ℕ} → (Fin n → B → ℝ) → (Fin n → B) → ℝ
  | 0, _, _ => 1
  | n + 1, u, xs =>
      (if ∃ i : Fin n, xs (Fin.last n) = xs i.castSucc then 1
        else u (Fin.last n) (xs (Fin.last n))) *
      retainedQueryWeight (fun i : Fin n => u i.castSucc) (fun i => xs i.castSucc)

theorem actual_repeat_mask {B : Type*} [DecidableEq B] {n : ℕ}
    (u : Fin n → B → ℝ) (xs : Fin n → B) (forbidden : Finset B)
    (havoid : ∀ a, xs a ∉ forbidden) :
    repeatMaskWeight (queryRepeatMask xs) u forbidden xs = retainedQueryWeight u xs := by
  induction n generalizing forbidden with
  | zero => rfl
  | succ n ih =>
    simp only [repeatMaskWeight, queryRepeatMask, Fin.snoc_last, Fin.snoc_castSucc,
      decide_eq_true_eq, retainedQueryWeight]
    by_cases hrep : ∃ i : Fin n, xs (Fin.last n) = xs i.castSucc
    · simp only [if_pos hrep, one_mul]
      exact ih _ _ forbidden (fun i => havoid i.castSucc)
    · simp only [if_neg hrep, if_neg (havoid (Fin.last n))]
      congr 1
      apply ih
      intro i
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun he => hrep ⟨i, he.symm⟩, havoid i.castSucc⟩

/-- Sum the masks after the conditional group and label comparisons. -/
theorem query_mask_expansion {B : Type*} [Fintype B] [DecidableEq B] {n : ℕ}
    (P : FinLaw (Fin n → B)) (u : Fin n → B → ℝ) (hu : ∀ a b, 0 ≤ u a b) :
    P.E (retainedQueryWeight u) ≤
      ∑ J : Fin n → Bool, P.E (repeatMaskWeight J u ∅) := by
  classical
  calc
    _ ≤ P.E (fun xs => ∑ J : Fin n → Bool, repeatMaskWeight J u ∅ xs) := by
      apply expect_le
      intro xs
      rw [← actual_repeat_mask u xs ∅ (fun _ => by simp)]
      exact Finset.single_le_sum
        (fun J _ => repeatMaskWeight_nonneg J u hu ∅ xs)
        (Finset.mem_univ (queryRepeatMask xs))
    _ = _ := by
      unfold FinLaw.E
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm

theorem mask_coefficient {n : ℕ} (J : Fin n → Bool) (μ : Fin n → ℝ) (δ : ℝ) :
    δ ^ maskDrops J * (∏ a, if J a then 1 else μ a) =
      ∏ a, if J a then δ else μ a := by
  induction n with
  | zero => simp [maskDrops]
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [maskDrops]
    cases hj : J (Fin.last n) with
    | true =>
      simp only [hj, if_true, pow_succ, mul_one]
      rw [← ih (fun i => J i.castSucc) (fun i => μ i.castSucc)]
      ring
    | false =>
      simp only [hj, Bool.false_eq_true, if_false, add_zero]
      rw [← ih (fun i => J i.castSucc) (fun i => μ i.castSucc)]
      ring

/-- Summing the repeat allowances produces one additive allowance in each
raw query mean, including the empty-query case. -/
theorem sum_masks {n : ℕ} (μ : Fin n → ℝ) (δ : ℝ) :
    (∑ J : Fin n → Bool, δ ^ maskDrops J * (∏ a, if J a then 1 else μ a)) =
      ∏ a, (μ a + δ) := by
  simp_rw [mask_coefficient]
  calc
    _ = ∏ a : Fin n, ∑ b : Bool, if b then δ else μ a :=
      (Fintype.prod_sum (fun (a : Fin n) (b : Bool) => if b then δ else μ a)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro a _
      simp [add_comm]

theorem maskDrops_le {n : ℕ} (J : Fin n → Bool) : maskDrops J ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have h := ih (fun i => J i.castSucc)
    cases hj : J (Fin.last n) <;> simp [maskDrops, hj] <;> omega

def keptTargets {B : Type*} [DecidableEq B] :
    {n : ℕ} → (Fin n → Bool) → (Fin n → B) → Finset B
  | 0, _, _ => ∅
  | n + 1, J, xs =>
      if J (Fin.last n) then keptTargets (fun i : Fin n => J i.castSucc) (fun i => xs i.castSucc)
      else insert (xs (Fin.last n)) (keptTargets (fun i : Fin n => J i.castSucc) (fun i => xs i.castSucc))

theorem kept_targets_cert {B : Type*} [DecidableEq B] {n : ℕ}
    (J : Fin n → Bool) (u : Fin n → B → ℝ) (forbidden : Finset B) (xs : Fin n → B)
    (hzero : keptMaskWeight J u forbidden xs ≠ 0) :
    (keptTargets J xs).card = n - maskDrops J ∧ Disjoint (keptTargets J xs) forbidden := by
  induction n generalizing forbidden with
  | zero => simp [keptTargets, maskDrops]
  | succ n ih =>
    let J' := fun i : Fin n => J i.castSucc
    let xs' := fun i : Fin n => xs i.castSucc
    let u' := fun i : Fin n => u i.castSucc
    cases hj : J (Fin.last n) with
    | true =>
      simp only [keptMaskWeight, hj, if_true] at hzero
      have h := ih J' u' forbidden xs' hzero
      simp only [keptTargets, maskDrops, hj, if_true]
      constructor
      · dsimp only [J', xs'] at h
        simpa only [Nat.add_sub_add_right] using h.1
      · exact h.2
    | false =>
      have hl : xs (Fin.last n) ∉ forbidden := by
        intro hl
        apply hzero
        simp [keptMaskWeight, hj, hl]
      simp only [keptMaskWeight, hj, Bool.false_eq_true, if_false, if_neg hl] at hzero
      have hprefix := (mul_ne_zero_iff.mp hzero).2
      have h := ih J' u' (insert (xs (Fin.last n)) forbidden) xs' hprefix
      have hnew : xs (Fin.last n) ∉ keptTargets J' xs' := by
        intro hx
        exact Finset.disjoint_left.mp h.2 hx (Finset.mem_insert_self _ _)
      simp only [keptTargets, maskDrops, hj, Bool.false_eq_true, if_false, add_zero]
      constructor
      · rw [Finset.card_insert_of_notMem hnew]
        dsimp only [J', xs'] at h
        rw [h.1]
        have hd := maskDrops_le (fun i : Fin n => J i.castSucc)
        omega
      · apply Finset.disjoint_left.mpr
        intro b hb hbf
        rcases Finset.mem_insert.mp hb with he | hb
        · subst b; exact hl hbf
        · exact Finset.disjoint_left.mp h.2 hb (Finset.mem_insert_of_mem hbf)

/-- Only retained targets require pool membership. -/
theorem kept_pool_mark {B : Type*} [DecidableEq B] {n : ℕ}
    (J : Fin n → Bool) (u : Fin n → B → ℝ) (pool forbidden : Finset B) (xs : Fin n → B) :
    keptMaskWeight J (fun a b => if b ∈ pool then u a b else 0) forbidden xs =
      if keptTargets J xs ⊆ pool then keptMaskWeight J u forbidden xs else 0 := by
  induction n generalizing forbidden with
  | zero => simp [keptMaskWeight, keptTargets]
  | succ n ih =>
    let J' := fun i : Fin n => J i.castSucc
    let xs' := fun i : Fin n => xs i.castSucc
    let u' := fun i : Fin n => u i.castSucc
    cases hj : J (Fin.last n) with
    | true =>
      simp only [keptMaskWeight, keptTargets, hj, if_true]
      exact ih J' u' forbidden xs'
    | false =>
      by_cases hl : xs (Fin.last n) ∈ forbidden
      · simp [keptMaskWeight, keptTargets, hj, hl]
      · simp only [keptMaskWeight, keptTargets, hj, Bool.false_eq_true, if_false, if_neg hl]
        rw [ih J' u' (insert (xs (Fin.last n)) forbidden) xs']
        by_cases hp : xs (Fin.last n) ∈ pool <;>
          by_cases hs : keptTargets J' xs' ⊆ pool <;>
          dsimp only [J', xs', u'] at hs ⊢ <;>
          simp [Finset.insert_subset_iff, hp, hs]

theorem expect_indicator {B : Type*} [Fintype B] (P : FinLaw B)
    (A : B → Prop) [DecidablePred A] (c : ℝ) :
    P.E (fun b => if A b then c else 0) = P.pr A * c := by
  classical
  unfold FinLaw.E FinLaw.pr
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : A b <;> simp [hb]

/-- The unforced iid containment probability cancels all retained
pool-restriction factors before distinctness is discarded. -/
theorem kept_iid_pool_cancellation {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (C : G.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (G.cellPatch C))).Nonempty)
    (hslot : 0 < G.nslot C) {n : ℕ} (J : Fin n → Bool)
    (Q : Fin n → FinLaw (Bin PT.tiling (G.cellPatch C)))
    (u : Fin n → Bin PT.tiling (G.cellPatch C) → ℝ) (hu : ∀ a b, 0 ≤ u a b) :
    (S16.iidCellPoolLaw (G := G) C hBins).E (fun pool =>
      ((Fintype.card (Bin PT.tiling (G.cellPatch C)) : ℝ) / G.nslot C) ^ (n - maskDrops J) *
        (FinLaw.pi Q).E (keptMaskWeight J
          (fun a b => if b ∈ Finset.univ.image pool then u a b else 0) ∅)) ≤
      (FinLaw.pi Q).E (keptMaskWeight J u ∅) := by
  classical
  let B : ℝ := Fintype.card (Bin PT.tiling (G.cellPatch C))
  let L : ℝ := G.nslot C
  let Scale : ℝ := B / L
  let m := n - maskDrops J
  let PoolLaw := S16.iidCellPoolLaw (G := G) C hBins
  have hB : 0 < B := by
    letI : Nonempty (Bin PT.tiling (G.cellPatch C)) := ⟨hBins.choose⟩
    dsimp [B]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Bin PT.tiling (G.cellPatch C)))
  have hL : 0 < L := by dsimp [L]; exact_mod_cast hslot
  have hCancel : Scale ^ m * (L / B) ^ m = 1 := by
    rw [← mul_pow]
    have hscalar : Scale * (L / B) = 1 := by
      dsimp [Scale]
      field_simp
    rw [hscalar, one_pow]
  have hswap : PoolLaw.E (fun pool => Scale ^ m *
      (FinLaw.pi Q).E (keptMaskWeight J
        (fun a b => if b ∈ Finset.univ.image pool then u a b else 0) ∅)) =
      (FinLaw.pi Q).E (fun xs => Scale ^ m * PoolLaw.E (fun pool =>
        keptMaskWeight J (fun a b => if b ∈ Finset.univ.image pool then u a b else 0) ∅ xs)) := by
    calc
      _ = PoolLaw.E (fun pool => (FinLaw.pi Q).E (fun xs => Scale ^ m *
          keptMaskWeight J (fun a b => if b ∈ Finset.univ.image pool then u a b else 0) ∅ xs)) := by
        simp_rw [expect_const_mul]
      _ = (FinLaw.pi Q).E (fun xs => PoolLaw.E (fun pool => Scale ^ m *
          keptMaskWeight J (fun a b => if b ∈ Finset.univ.image pool then u a b else 0) ∅ xs)) :=
        expect_indep_comm _ _ _
      _ = _ := by simp_rw [expect_const_mul]
  change PoolLaw.E (fun pool => Scale ^ m * (FinLaw.pi Q).E _) ≤ _
  rw [hswap]
  apply expect_le
  intro xs
  simp_rw [kept_pool_mark]
  rw [expect_indicator PoolLaw
    (fun pool => keptTargets J xs ⊆ Finset.univ.image pool) (keptMaskWeight J u ∅ xs)]
  by_cases hz : keptMaskWeight J u ∅ xs = 0
  · simp [hz]
  have hc := (kept_targets_cert J u ∅ xs hz).1
  have hContain := S16.iid_distinct_bin_containment (G := G) C hBins (keptTargets J xs)
  rw [hc] at hContain
  have hw := keptMaskWeight_nonneg J u hu ∅ xs
  calc
    Scale ^ m * (PoolLaw.pr (fun pool => keptTargets J xs ⊆ Finset.univ.image pool) *
        keptMaskWeight J u ∅ xs) =
        (Scale ^ m * PoolLaw.pr (fun pool => keptTargets J xs ⊆ Finset.univ.image pool)) *
          keptMaskWeight J u ∅ xs := by ring
    _ ≤ (Scale ^ m * (L / B) ^ m) * keptMaskWeight J u ∅ xs := by
      apply mul_le_mul_of_nonneg_right _ hw
      exact mul_le_mul_of_nonneg_left hContain (pow_nonneg (div_nonneg hB.le hL.le) _)
    _ = _ := by rw [hCancel, one_mul]

theorem kept_bit_no_earlier {B : Type*} [DecidableEq B] {n : ℕ}
    (xs : Fin n → B) (a : Fin n) (ha : queryRepeatMask xs a = false) :
    ∀ b, b < a → xs b ≠ xs a := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    cases a using Fin.lastCases with
    | last =>
      have hrep : ¬ ∃ i : Fin n, xs (Fin.last n) = xs i.castSucc := by
        simpa [queryRepeatMask] using ha
      intro b hb
      cases b using Fin.lastCases with
      | last => exact (lt_irrefl _ hb).elim
      | cast b => exact fun he => hrep ⟨b, he.symm⟩
    | cast a =>
      have ha' : queryRepeatMask (fun i : Fin n => xs i.castSucc) a = false := by
        simpa [queryRepeatMask] using ha
      have h := ih (fun i : Fin n => xs i.castSucc) a ha'
      intro b hb
      cases b using Fin.lastCases with
      | last =>
        have hh := a.isLt
        simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc] at hb
        omega
      | cast b =>
        exact h b (by simpa only [Fin.lt_def, Fin.val_castSucc] using hb)

theorem retained_bins_injective {B : Type*} [DecidableEq B] {n : ℕ} (xs : Fin n → B) :
    Set.InjOn xs {a | queryRepeatMask xs a = false} := by
  intro a ha b hb he
  rcases lt_trichotomy a b with hab | hab | hba
  · exact ((kept_bit_no_earlier xs b hb a hab) he).elim
  · exact hab
  · exact ((kept_bit_no_earlier xs a ha b hba) he.symm).elim

/-- The actual retained role scope has at most one role in any physical bin. -/
theorem retained_role_bin_count {Role Group B : Type*} [DecidableEq Role] [DecidableEq B]
    {n : ℕ} (r : Fin n → Role) (g : Role → Group) (bins : Group → B) (b : B) :
    (((Finset.univ.filter fun a => queryRepeatMask (fun a => bins (g (r a))) a = false).image r).filter
      (fun v => bins (g v) = b)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  obtain ⟨hvScope, hvBin⟩ := Finset.mem_filter.mp hv
  obtain ⟨hwScope, hwBin⟩ := Finset.mem_filter.mp hw
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hvScope
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hwScope
  have he : a = a' := retained_bins_injective (fun a => bins (g (r a)))
    (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp ha').2 (hvBin.trans hwBin.symm)
  rw [he]

theorem retained_weight_product {B : Type*} [DecidableEq B] {n : ℕ}
    (u : Fin n → B → ℝ) (xs : Fin n → B) :
    retainedQueryWeight u xs = ∏ a, if queryRepeatMask xs a then 1 else u a (xs a) := by
  induction n with
  | zero => simp [retainedQueryWeight]
  | succ n ih =>
    simp only [retainedQueryWeight, Fin.prod_univ_castSucc, queryRepeatMask,
      Fin.snoc_castSucc, Fin.snoc_last, decide_eq_true_eq]
    rw [ih (fun i => u i.castSucc) (fun i => xs i.castSucc)]
    ring

theorem product_kept {n : ℕ} (J : Fin n → Bool) (f : Fin n → ℝ) :
    (∏ a, if J a then 1 else f a) =
      ∏ a ∈ Finset.univ.filter (fun a => J a = false), f a := by
  have h (a : Fin n) : (if J a then (1 : ℝ) else f a) =
      if J a = false then f a else 1 := by cases hj : J a <;> simp [hj]
  simp_rw [h]
  rw [Finset.prod_ite]
  simp

theorem retainedQueryWeight_nonneg {B : Type*} [DecidableEq B] {n : ℕ}
    (u : Fin n → B → ℝ) (hu : ∀ a b, 0 ≤ u a b) (xs : Fin n → B) :
    0 ≤ retainedQueryWeight u xs := by
  rw [retained_weight_product]
  apply Finset.prod_nonneg
  intro a _
  split_ifs
  · exact zero_le_one
  · exact hu _ _

theorem expect_le_on_support {A : Type*} [Fintype A] (P : FinLaw A)
    (f g : A → ℝ) (h : ∀ a, P.w a ≠ 0 → f a ≤ g a) : P.E f ≤ P.E g := by
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : P.w a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonneg_left (h a ha) (P.nonneg a)

theorem atom_expect_comparison {B : Type*} [Fintype B] [DecidableEq B]
    (P Q : FinLaw B) (pool : Finset B) (c : ℝ)
    (hcap : ∀ b, P.w b ≤ if b ∈ pool then c * Q.w b else 0)
    (f : B → ℝ) (hf : ∀ b, 0 ≤ f b) :
    P.E f ≤ c * Q.E (fun b => if b ∈ pool then f b else 0) := by
  classical
  unfold FinLaw.E
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  have h := mul_le_mul_of_nonneg_right (hcap b) (hf b)
  by_cases hb : b ∈ pool
  · simpa only [if_pos hb, mul_assoc] using h
  · simpa only [if_neg hb, zero_mul, mul_zero] using h

/-- Replace only retained restricted atoms by their raw kernels. Removed
coordinates integrate to one and incur no pool-restriction factor. -/
theorem kept_atom_comparison {B : Type*} [Fintype B] [DecidableEq B] {n : ℕ}
    (P Q : Fin n → FinLaw B) (pool : Finset B) (c : ℝ) (hc : 0 ≤ c)
    (hcap : ∀ a b, (P a).w b ≤ if b ∈ pool then c * (Q a).w b else 0)
    (J : Fin n → Bool) (u : Fin n → B → ℝ) (hu : ∀ a b, 0 ≤ u a b)
    (forbidden : Finset B) :
    (FinLaw.pi P).E (keptMaskWeight J u forbidden) ≤
      c ^ (n - maskDrops J) * (FinLaw.pi Q).E
        (keptMaskWeight J (fun a b => if b ∈ pool then u a b else 0) forbidden) := by
  classical
  induction n generalizing forbidden with
  | zero => simp [keptMaskWeight, maskDrops, expect_const]
  | succ n ih =>
    let P' := fun i : Fin n => P i.castSucc
    let Q' := fun i : Fin n => Q i.castSucc
    let J' := fun i : Fin n => J i.castSucc
    let u' := fun i : Fin n => u i.castSucc
    let v' := fun i : Fin n => fun b => if b ∈ pool then u' i b else 0
    have hcap' : ∀ a b, (P' a).w b ≤ if b ∈ pool then c * (Q' a).w b else 0 :=
      fun a b => hcap a.castSucc b
    have hu' : ∀ a b, 0 ≤ u' a b := fun a b => hu a.castSucc b
    have hv' : ∀ a b, 0 ≤ v' a b := by
      intro a b
      dsimp only [v']
      split_ifs <;> first | exact hu' a b | exact le_rfl
    have hprefix (S : Finset B) := ih P' Q' hcap' J' u' hu' S
    cases hj : J (Fin.last n) with
    | true =>
      rw [pi_E_snoc, pi_E_snoc]
      simp only [keptMaskWeight, hj, if_true, Fin.snoc_castSucc, expect_const,
        maskDrops, Nat.add_sub_add_right]
      exact hprefix forbidden
    | false =>
      let H := fun b => if b ∈ forbidden then 0 else
        u (Fin.last n) b * (FinLaw.pi Q').E (keptMaskWeight J' v' (insert b forbidden))
      have hH : ∀ b, 0 ≤ H b := by
        intro b
        dsimp [H]
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (hu _ _) (expect_nonneg _ _ (keptMaskWeight_nonneg J' v' hv' _))
      have hLeft : (FinLaw.pi P).E (keptMaskWeight J u forbidden) ≤
          c ^ (n - maskDrops J') * (P (Fin.last n)).E H := by
        rw [pi_E_snoc, ← expect_const_mul]
        apply expect_le
        intro b
        by_cases hb : b ∈ forbidden
        · simp [keptMaskWeight, hj, Fin.snoc_last, hb, H, expect_const]
        · simp only [keptMaskWeight, hj, Bool.false_eq_true, if_false, Fin.snoc_last,
            if_neg hb, Fin.snoc_castSucc, H]
          rw [expect_const_mul]
          have h := mul_le_mul_of_nonneg_left (hprefix (insert b forbidden)) (hu (Fin.last n) b)
          simpa only [mul_left_comm] using h
      have hOuter := atom_expect_comparison (P (Fin.last n)) (Q (Fin.last n)) pool c
        (hcap (Fin.last n)) H hH
      have hRight : (FinLaw.pi Q).E
          (keptMaskWeight J (fun a b => if b ∈ pool then u a b else 0) forbidden) =
          (Q (Fin.last n)).E (fun b => if b ∈ pool then H b else 0) := by
        rw [pi_E_snoc]
        apply congrArg
        funext b
        by_cases hf : b ∈ forbidden
        · simp [keptMaskWeight, hj, Fin.snoc_last, H, hf, expect_const]
        · by_cases hp : b ∈ pool
          · simp only [keptMaskWeight, hj, Bool.false_eq_true, if_false, Fin.snoc_last,
              Fin.snoc_castSucc, H, if_neg hf, if_pos hp]
            exact expect_const_mul _ _ _
          · simp [keptMaskWeight, hj, Fin.snoc_last, H, hf, hp, expect_const]
      calc
        _ ≤ c ^ (n - maskDrops J') * (P (Fin.last n)).E H := hLeft
        _ ≤ c ^ (n - maskDrops J') * (c * (Q (Fin.last n)).E (fun b => if b ∈ pool then H b else 0)) :=
          mul_le_mul_of_nonneg_left hOuter (pow_nonneg hc _)
        _ = _ := by
          rw [← hRight]
          have hd := maskDrops_le J'
          have he : n + 1 - maskDrops J' = (n - maskDrops J') + 1 := by omega
          simp only [maskDrops, hj, Bool.false_eq_true, if_false, add_zero]
          change _ = c ^ (n + 1 - maskDrops J') * _
          rw [he, pow_succ]
          ring

theorem kept_weight_le_product {B : Type*} [DecidableEq B] {n : ℕ}
    (J : Fin n → Bool) (u : Fin n → B → ℝ) (hu : ∀ a b, 0 ≤ u a b)
    (forbidden : Finset B) (xs : Fin n → B) :
    keptMaskWeight J u forbidden xs ≤ ∏ a, if J a then 1 else u a (xs a) := by
  induction n generalizing forbidden with
  | zero => simp [keptMaskWeight]
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    cases hj : J (Fin.last n) with
    | true =>
      simp only [keptMaskWeight, hj, if_true, mul_one]
      exact ih _ _ (fun i b => hu i.castSucc b) _ _
    | false =>
      simp only [keptMaskWeight, hj, Bool.false_eq_true, if_false]
      split_ifs
      · apply mul_nonneg
        · exact Finset.prod_nonneg (fun i _ => by split_ifs; exact zero_le_one; exact hu _ _)
        · exact hu _ _
      · have h := mul_le_mul_of_nonneg_left
          (ih (fun i : Fin n => J i.castSucc) (fun i : Fin n => u i.castSucc)
            (fun i b => hu i.castSucc b) (insert (xs (Fin.last n)) forbidden)
            (fun i : Fin n => xs i.castSucc)) (hu (Fin.last n) (xs (Fin.last n)))
        simpa only [mul_comm] using h

theorem kept_expect_product_le {B : Type*} [Fintype B] [DecidableEq B] {n : ℕ}
    (P : Fin n → FinLaw B) (J : Fin n → Bool) (u : Fin n → B → ℝ)
    (hu : ∀ a b, 0 ≤ u a b) :
    (FinLaw.pi P).E (keptMaskWeight J u ∅) ≤
      ∏ a, if J a then 1 else (P a).E (u a) := by
  calc
    _ ≤ (FinLaw.pi P).E (fun xs => ∏ a, if J a then 1 else u a (xs a)) :=
      expect_le _ _ _ (kept_weight_le_product J u hu ∅)
    _ = ∏ a, (P a).E (fun b => if J a then 1 else u a b) :=
      S16.Lane_q_s16_comp2.pi_expect_prod P (fun a b => if J a then 1 else u a b)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro a _
      cases hj : J a <;> simp [hj, expect_const]

/-- Average retained restricted atoms over unforced iid pools. The small
denominator price remains, while B/L factors cancel against containment. -/
theorem kept_typical_pool_comparison {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (C : G.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (G.cellPatch C))).Nonempty)
    (hslot : 0 < G.nslot C) {q : ℕ} (J : Fin q → Bool)
    (Q : Fin q → FinLaw (Bin PT.tiling (G.cellPatch C)))
    (P : CellPool G C → Fin q → FinLaw (Bin PT.tiling (G.cellPatch C)))
    (typical : CellPool G C → Prop) (c : ℝ) (hc : 0 ≤ c)
    (hcap : ∀ pool, typical pool → ∀ a b, (P pool a).w b ≤
      if b ∈ Finset.univ.image pool then
        (c * ((Fintype.card (Bin PT.tiling (G.cellPatch C)) : ℝ) / G.nslot C)) * (Q a).w b else 0)
    (u : Fin q → Bin PT.tiling (G.cellPatch C) → ℝ) (hu : ∀ a b, 0 ≤ u a b) :
    (S16.iidCellPoolLaw (G := G) C hBins).E (fun pool => if typical pool then
      (FinLaw.pi (P pool)).E (keptMaskWeight J u ∅) else 0) ≤
        c ^ (q - maskDrops J) * (FinLaw.pi Q).E (keptMaskWeight J u ∅) := by
  classical
  let Scale : ℝ := Fintype.card (Bin PT.tiling (G.cellPatch C)) / (G.nslot C : ℝ)
  let m := q - maskDrops J
  have hs : 0 ≤ Scale := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hpoint (pool : CellPool G C) :
      (if typical pool then (FinLaw.pi (P pool)).E (keptMaskWeight J u ∅) else 0) ≤
      c ^ m * (Scale ^ m * (FinLaw.pi Q).E
        (keptMaskWeight J (fun a b => if b ∈ Finset.univ.image pool then u a b else 0) ∅)) := by
    by_cases ht : typical pool
    · rw [if_pos ht]
      have h := kept_atom_comparison (P pool) Q (Finset.univ.image pool) (c * Scale)
        (mul_nonneg hc hs) (hcap pool ht) J u hu ∅
      simpa only [mul_pow, mul_assoc] using h
    · rw [if_neg ht]
      apply mul_nonneg (pow_nonneg hc _)
      apply mul_nonneg (pow_nonneg hs _)
      apply expect_nonneg
      apply keptMaskWeight_nonneg
      intro a b
      split_ifs <;> first | exact hu a b | exact le_rfl
  calc
    _ ≤ (S16.iidCellPoolLaw (G := G) C hBins).E (fun pool =>
        c ^ m * (Scale ^ m * (FinLaw.pi Q).E
          (keptMaskWeight J (fun a b => if b ∈ Finset.univ.image pool then u a b else 0) ∅))) :=
      expect_le _ _ _ hpoint
    _ = c ^ m * (S16.iidCellPoolLaw (G := G) C hBins).E (fun pool => Scale ^ m *
        (FinLaw.pi Q).E (keptMaskWeight J
          (fun a b => if b ∈ Finset.univ.image pool then u a b else 0) ∅)) := expect_const_mul _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (kept_iid_pool_cancellation C hBins hslot J Q u hu)
      (pow_nonneg hc _)

theorem expect_if_const {A : Type*} [Fintype A] (P : FinLaw A) (b : Prop)
    [Decidable b] (f : A → ℝ) :
    P.E (fun a => if b then f a else 0) = if b then P.E f else 0 := by
  by_cases hb : b <;> simp [hb, expect_const]

theorem expect_sum {A I : Type*} [Fintype A] [Fintype I]
    (P : FinLaw A) (f : I → A → ℝ) :
    P.E (fun a => ∑ i, f i a) = ∑ i, P.E (f i) := by
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

end HypercubeRamsey.S18.Lane_sol_d18l_cal
