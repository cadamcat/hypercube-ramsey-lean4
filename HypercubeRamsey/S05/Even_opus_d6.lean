import HypercubeRamsey.S05.Even_load_height_scales_sol_s05_even
import HypercubeRamsey.S05.Even_load_cancel_sol_s05_even
import HypercubeRamsey.S05.Even_load_empirical_sol_s05_even

/-!
# D6 helpers (lane opus-s05-d6): forced-centre selection sums and the comparison-mean pieces

Generic pieces for `Lane_opus_s05_even.evenW_mean` (05:1209–1247): star marginalization of product odd laws,
the forced-centre selection bound per prospective center (level zero `3/λ`, positive levels the forced-center
height estimate), its sum over centers (`3 + λ(H+1)ε`), and the tuple marginal at a selected reference
(subtuple ratio against the full array, `P̄_K ≤ B_K/N` at prior-light labels).
-/

namespace HypercubeRamsey.Setup5.Lane_opus_s05_d6

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

/-! ### Generic finite-probability facts -/

/-- A product expectation of a function of the coordinates in `S` is a sum over the `S`-outputs. -/
theorem pi_expect_star {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (P : I → FinProb O) (S : Finset I) (o₀ : O) (G : (I → O) → ℝ)
    (hG : FinProb.DependsOn G S) :
    (FinProb.pi P).expect G =
      ∑ d : S → O, (∏ i ∈ S, (P i).w (Lane_sol_s05_even.extendOutputs S o₀ d i)) *
        G (Lane_sol_s05_even.extendOutputs S o₀ d) := by
  rw [FinProb.pi_expect_depends P S G (fun _ => o₀) hG]
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro d _
  rw [Lane_sol_s05_even.pi_query_weight S P o₀ d]
  rfl

theorem prod_pr_nested {α β : Type*} [Fintype α] [Fintype β] (P : FinProb α) (Q : FinProb β)
    (B : α × β → Prop) [DecidablePred B] :
    (P.prod Q).pr B = P.expect (fun a => Q.expect (fun b => if B (a, b) then (1 : ℝ) else 0)) := by
  unfold FinProb.pr FinProb.expect
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hB : B (a, b)
  · simp only [hB, if_true, mul_one]
    rfl
  · simp only [hB, if_false, mul_zero]

theorem prod_unit_pr_nested {α β : Type*} [Fintype α] [Fintype β] (P : FinProb α) (U : FinProb Unit)
    (Q : FinProb β) (B : (α × Unit) × β → Prop) [DecidablePred B] :
    ((P.prod U).prod Q).pr B =
      P.expect (fun a => Q.expect (fun b => if B ((a, ()), b) then (1 : ℝ) else 0)) := by
  have hU : U.w () = 1 := by simpa using U.sum_eq_one
  unfold FinProb.pr FinProb.expect
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_unique, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hd : (default : Unit) = () := rfl
  by_cases hB : B ((a, ()), b)
  · simp only [hd, hB, if_true, mul_one]
    show P.w a * U.w () * Q.w b = P.w a * Q.w b
    rw [hU, mul_one]
  · simp only [hd, hB, if_false, mul_zero]

/-! ### Forced-centre selection (05:1220–1238) -/

/-- The selection probability of one prospective center at fixed arrays: forced presence costs `λ/V`; at level
zero the eligible-active tie bound is `3/λ`; at a positive level the forced-center height estimate `ε`. -/
theorem selection_point_bound (p : HDParams) (hlam : 0 < p.lam) (Sites : p.Sites) (v : CubeVertex p.d)
    (hv : v ∈ Sites) (E : (p.Loc → Bool) → p.EligMap)
    (hshape : ∀ P j l, l ∈ E P v j → l.2 = j) (l : p.Loc) (U : FinProb Unit) (ε : ℝ)
    (hpos : (((p.posLawForced (some l)).prod U).prod p.actLaw).pr (fun ω =>
      p.Legal ω.1.1 (E ω.1.1) (p.domBall Sites v p.Rlong) ∧
        0 < p.height Sites ω.1.1 ω.2 (E ω.1.1) p.Rlong v) ≤ ε) :
    p.posLaw.expect (fun P => p.actLaw.expect (fun A => p.tieLaw.expect (fun T =>
      if p.Legal P (E P) (p.domBall Sites v p.Rlong) ∧ p.selection Sites P A (E P) T v = some l
      then (1 : ℝ) else 0))) ≤
    p.lam / p.V * ((if l.2.val = 0 ∧ _root_.hammingDist l.1 v ≤ p.r then 3 / p.lam else 0) +
      (if _root_.hammingDist l.1 v ≤ p.r then ε else 0)) := by
  have hvdom : v ∈ p.domBall Sites v p.Rlong := Finset.mem_filter.mpr ⟨hv, by simp⟩
  have hev : ∀ P A T, p.Legal P (E P) (p.domBall Sites v p.Rlong) →
      p.selection Sites P A (E P) T v = some l →
      P l = true ∧ _root_.hammingDist l.1 v ≤ p.r ∧ l.2.val = p.height Sites P A (E P) p.Rlong v := by
    intro P A T hL hs
    obtain ⟨j, hj, hjh⟩ := Lane_sol_s05_even.selectionAt_some_mem_level p Sites P A (E P) T p.Rlong v l hs
    have hleg := (hL v hvdom j).1 l hj
    exact ⟨hleg.1, hleg.2.2, (congrArg Fin.val hleg.2.1).trans hjh⟩
  let ind : (p.Loc → Bool) → (p.Loc → Bool) → p.Ties → ℝ := fun P A T =>
    if p.Legal P (E P) (p.domBall Sites v p.Rlong) ∧ p.selection Sites P A (E P) T v = some l
    then (1 : ℝ) else 0
  let f : (p.Loc → Bool) → ℝ := fun P => p.actLaw.expect (fun A => p.tieLaw.expect (fun T => ind P A T))
  let fp : (p.Loc → Bool) → ℝ := fun P => p.actLaw.expect (fun A =>
    if p.Legal P (E P) (p.domBall Sites v p.Rlong) ∧ 0 < p.height Sites P A (E P) p.Rlong v
    then (1 : ℝ) else 0)
  let c0 : ℝ := if l.2.val = 0 ∧ _root_.hammingDist l.1 v ≤ p.r then 3 / p.lam else 0
  let g : (p.Loc → Bool) → ℝ := fun P => c0 + (if _root_.hammingDist l.1 v ≤ p.r then fp P else 0)
  have hind0 : ∀ P A T, 0 ≤ ind P A T := fun P A T => by
    simp only [ind]; split_ifs <;> norm_num
  have hfp0 : ∀ P, 0 ≤ fp P := fun P => by
    simp only [fp, FinProb.expect]
    exact Finset.sum_nonneg fun A _ => mul_nonneg (p.actLaw.nonneg A) (by split_ifs <;> norm_num)
  have hc0 : 0 ≤ c0 := by
    simp only [c0]; split_ifs
    · exact div_nonneg (by norm_num) hlam.le
    · exact le_refl 0
  have hzero : ∀ P, (∀ A T, ind P A T = 0) → f P = 0 := by
    intro P h
    simp only [f, h, FinProb.expect_const]
  have hpoint : ∀ P, f P ≤ if P l = true then g P else 0 := by
    intro P
    by_cases hPl : P l = true
    · rw [if_pos hPl]
      by_cases hd : _root_.hammingDist l.1 v ≤ p.r
      · by_cases hl0 : l.2.val = 0
        · have hc0eq : c0 = 3 / p.lam := if_pos ⟨hl0, hd⟩
          have hb := Lane_sol_s05_even.level_zero_selection_bound p hlam P (E P) Sites v hv l hl0
            (hshape P)
          rw [prod_pr_nested] at hb
          have hgP : g P = 3 / p.lam + fp P := by simp only [g, hc0eq, if_pos hd]
          rw [hgP]
          exact hb.trans (le_add_of_nonneg_right (hfp0 P))
        · have hgP : g P = c0 + fp P := by simp only [g, if_pos hd]
          rw [hgP]
          refine le_trans ?_ (le_add_of_nonneg_left hc0)
          apply FinProb.expect_mono
          intro A
          have hT : ∀ T, ind P A T ≤ (if p.Legal P (E P) (p.domBall Sites v p.Rlong) ∧
              0 < p.height Sites P A (E P) p.Rlong v then (1 : ℝ) else 0) := by
            intro T
            simp only [ind]
            by_cases he : p.Legal P (E P) (p.domBall Sites v p.Rlong) ∧
                p.selection Sites P A (E P) T v = some l
            · have hh := (hev P A T he.1 he.2).2.2
              rw [if_pos he, if_pos ⟨he.1, by omega⟩]
            · rw [if_neg he]; split_ifs <;> norm_num
          calc
            p.tieLaw.expect (fun T => ind P A T) ≤ p.tieLaw.expect (fun _ =>
                (if p.Legal P (E P) (p.domBall Sites v p.Rlong) ∧
                  0 < p.height Sites P A (E P) p.Rlong v then (1 : ℝ) else 0)) :=
              FinProb.expect_mono _ hT
            _ = _ := FinProb.expect_const _ _
      · have hf0 : f P = 0 := hzero P (fun A T => by
          simp only [ind]
          rw [if_neg]
          intro he
          exact hd (hev P A T he.1 he.2).2.1)
        rw [hf0]
        exact add_nonneg hc0 (by rw [if_neg hd])
    · rw [if_neg hPl]
      exact le_of_eq (hzero P (fun A T => by
        simp only [ind]
        rw [if_neg]
        intro he
        exact hPl (hev P A T he.1 he.2).1))
  have hq : 0 ≤ p.lam / (p.V : ℝ) := div_nonneg hlam.le (Nat.cast_nonneg _)
  have hforced : (Lane_sol_s05_even.forcedPresenceLaw (p.lam / (p.V : ℝ)) l).expect fp =
      (p.posLawForced (some l)).expect fp := by
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro P _
    congr 1
    change (∏ i, _) = ∏ i, _
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i = l
    · subst hi; simp
    · have hne : ¬ (some l = some i) := fun h => hi (Option.some_injective _ h).symm
      simp [hi, hne]
  have hfpbound : (p.posLawForced (some l)).expect fp ≤ ε := by
    rw [prod_unit_pr_nested] at hpos
    exact hpos
  calc
    p.posLaw.expect f ≤ p.posLaw.expect (fun P => if P l = true then g P else 0) :=
      FinProb.expect_mono _ hpoint
    _ = max 0 (min (p.lam / (p.V : ℝ)) 1) *
        (Lane_sol_s05_even.forcedPresenceLaw (p.lam / (p.V : ℝ)) l).expect g :=
      Lane_sol_s05_even.forced_presence_expect (p.lam / (p.V : ℝ)) l g
    _ ≤ p.lam / p.V * (c0 + (if _root_.hammingDist l.1 v ≤ p.r then ε else 0)) := by
      have hg : (Lane_sol_s05_even.forcedPresenceLaw (p.lam / (p.V : ℝ)) l).expect g ≤
          c0 + (if _root_.hammingDist l.1 v ≤ p.r then ε else 0) := by
        simp only [g]
        rw [FinProb.expect_add, FinProb.expect_const]
        apply add_le_add (le_refl _)
        by_cases hd : _root_.hammingDist l.1 v ≤ p.r
        · simp only [if_pos hd]
          rw [hforced]
          exact hfpbound
        · simp only [if_neg hd, FinProb.expect_const, le_refl]
      have hg0 : 0 ≤ (Lane_sol_s05_even.forcedPresenceLaw (p.lam / (p.V : ℝ)) l).expect g := by
        unfold FinProb.expect
        exact Finset.sum_nonneg fun P _ => mul_nonneg (FinProb.nonneg _ P)
          (add_nonneg hc0 (by split_ifs; exact hfp0 P; exact le_refl 0))
      have hmax : max 0 (min (p.lam / (p.V : ℝ)) 1) ≤ p.lam / p.V :=
        max_le hq (min_le_left _ _)
      exact (mul_le_mul_of_nonneg_right hmax hg0).trans (mul_le_mul_of_nonneg_left hg hq)

/-- Summing the per-center bounds: `λ/V (3/λ · V + ε · V (H + 1)) = 3 + λ (H + 1) ε` (radius at most the
dimension, so the ball has volume `V`). -/
theorem selection_sum_bound (p : HDParams) (hlam : 0 < p.lam) (hr : p.r ≤ p.d) (v : CubeVertex p.d)
    (ε : ℝ) :
    ∑ l : p.Loc, p.lam / p.V * ((if l.2.val = 0 ∧ _root_.hammingDist l.1 v ≤ p.r then 3 / p.lam else 0) +
      (if _root_.hammingDist l.1 v ≤ p.r then ε else 0)) = 3 + p.lam * (p.H + 1) * ε := by
  have hball' : (Finset.univ.filter fun u : CubeVertex p.d => _root_.hammingDist u v ≤ p.r).card = p.V :=
    Lane_p_height_main.cube_ball_card_eq_choose_sum v hr
  have hball : ((Finset.univ.filter fun u : CubeVertex p.d => _root_.hammingDist u v ≤ p.r).card : ℝ) =
      p.V := by
    exact_mod_cast hball'
  have hV : (0 : ℝ) < p.V := by
    have h1 : 1 ≤ p.V := by
      unfold HDParams.V
      calc 1 = Nat.choose p.d 0 := (Nat.choose_zero_right _).symm
        _ ≤ ∑ i ∈ Finset.range (p.r + 1), Nat.choose p.d i :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _) (by simp)
    exact_mod_cast h1
  have hsum0 : (∑ l : p.Loc, (if l.2.val = 0 ∧ _root_.hammingDist l.1 v ≤ p.r then 3 / p.lam else 0)) =
      p.V * (3 / p.lam) := by
    rw [Fintype.sum_prod_type]
    have hinner (u : CubeVertex p.d) : (∑ j : Fin (p.H + 1),
        (if j.val = 0 ∧ _root_.hammingDist u v ≤ p.r then 3 / p.lam else 0)) =
        if _root_.hammingDist u v ≤ p.r then 3 / p.lam else 0 := by
      rw [Fin.sum_univ_succ]
      simp
    simp_rw [hinner]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hball]
  have hsum1 : (∑ l : p.Loc, (if _root_.hammingDist l.1 v ≤ p.r then ε else 0)) =
      p.V * (p.H + 1) * ε := by
    rw [Fintype.sum_prod_type]
    have hinner (u : CubeVertex p.d) : (∑ _j : Fin (p.H + 1),
        (if _root_.hammingDist u v ≤ p.r then ε else 0)) =
        ((p.H : ℝ) + 1) * (if _root_.hammingDist u v ≤ p.r then ε else 0) := by
      simp
    simp_rw [hinner]
    rw [← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hball]
    ring
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hsum0, hsum1]
  have hVne : (p.V : ℝ) ≠ 0 := hV.ne'
  have hlne : p.lam ≠ 0 := hlam.ne'
  first
  | (field_simp; ring)
  | field_simp

/-! ### Level count and the stretched-exponential error -/

private theorem power_reaches' (M R t : ℕ) (hM : 2 ≤ M) (hR : 1 ≤ R) : ∃ j, t ≤ M ^ j * R := by
  induction t with
  | zero => exact ⟨0, by omega⟩
  | succ t ih =>
    obtain ⟨j, hj⟩ := ih
    have hp : 1 ≤ M ^ j * R := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega))
    refine ⟨j + 1, ?_⟩
    rw [pow_succ]
    nlinarith

theorem topScale_le {n : ℕ} (hn : 2 ≤ n) {σ ζ : ℝ} (hσ : σ ≤ 1) (hζ : 0 ≤ ζ) :
    topScale n σ ζ ≤ 4 * n ^ 2 := by
  let R : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let t : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlogLe : Real.log (n : ℝ) ≤ n :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hR : R ≤ n ^ 2 := by
    apply max_le (by nlinarith)
    apply Nat.ceil_le.mpr
    push_cast
    nlinarith
  have hM : M ≤ 2 * n := by
    apply max_le (by omega)
    apply Nat.ceil_le.mpr
    have hp : (n : ℝ) ^ σ ≤ n := by
      simpa using Real.rpow_le_rpow_of_exponent_le hnR hσ
    push_cast
    linarith
  have ht : t ≤ n := by
    apply Nat.ceil_le.mpr
    simpa using Real.rpow_le_rpow_of_exponent_le hnR (by linarith : 1 - ζ ≤ 1)
  let hex : ∃ j, t ≤ M ^ j * R := power_reaches' M R t (le_max_left _ _) (le_max_left _ _)
  change M ^ Nat.find hex * R ≤ 4 * n ^ 2
  by_cases hj : Nat.find hex = 0
  · simp only [hj, pow_zero, one_mul]
    nlinarith [hR]
  · have hprev : M ^ (Nat.find hex - 1) * R < t :=
      lt_of_not_ge (Nat.find_min hex (by omega))
    have hpow : M ^ Nat.find hex * R = M * (M ^ (Nat.find hex - 1) * R) := by
      have hi : Nat.find hex = (Nat.find hex - 1) + 1 := by omega
      conv_lhs => rw [hi]
      rw [pow_succ]
      ring
    rw [hpow]
    nlinarith

theorem eventually_height_error (c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, 5 * (n : ℝ) ^ (12 : ℕ) * Real.exp (-(n : ℝ) ^ c) ≤ 1 := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (12 / c) 1 (by norm_num)).comp hpow
  have heq (n : ℕ) : ((n : ℝ) ^ c) ^ (12 / c) = (n : ℝ) ^ (12 : ℕ) := by
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    rw [show c * (12 / c) = 12 by field_simp]
    norm_cast
  have hlim' : Tendsto (fun n : ℕ => 5 * (n : ℝ) ^ (12 : ℕ) *
      Real.exp (-(n : ℝ) ^ c)) atTop (nhds 0) := by
    have hh := hlim.const_mul 5
    simpa [heq, mul_assoc] using hh
  obtain ⟨n₀, h⟩ := eventually_atTop.mp (hlim'.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  exact ⟨n₀, fun n hn => (h n hn).le⟩


/-! ### Centers: array marginals, selected tuples and the per-center selection mean -/

theorem pi_expect_coord {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (i : ι) (F : Ω i → ℝ) :
    (FinProb.pi P).expect (fun ω => F (ω i)) = (P i).expect F := by
  classical
  let J := {j // j ∈ ({i} : Finset ι)}
  let j₀ : J := ⟨i, Finset.mem_singleton_self i⟩
  have h := FinProb.pi_marginal_expect P {i} (fun a => F (a j₀))
  refine h.trans ?_
  letI : Unique J := { default := j₀, uniq := fun j => Subtype.ext (Finset.mem_singleton.mp j.2) }
  unfold FinProb.expect
  rw [← (Equiv.piUnique (fun j : J => Ω j.1)).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  change (∏ j : J, (P j.1).w ((Equiv.piUnique (fun j : J => Ω j.1)).symm b j)) *
    F ((Equiv.piUnique (fun j : J => Ω j.1)).symm b j₀) = (P i).w b * F b
  rw [Fintype.prod_unique]
  rfl

theorem expect_sum {α ι : Type*} [Fintype α] [Fintype ι] (P : FinProb α) (f : ι → α → ℝ) :
    P.expect (fun a => ∑ i, f i a) = ∑ i, P.expect (f i) := by
  unfold FinProb.expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

/-- Iid arrays of `P_K`-blocks: the mean empirical frequency of a label is at most `P̄_K` (equality when the
array is nonempty). -/
theorem centre_array_marginal (h : X.HeightChoice5) (H : X.KeyHist) (l : h.hp.Loc) (K : X.Ty) (x : Fin N) :
    (Lane_sol_s05_even.centreArrayLaw X h H).expect
      (fun B => Lane_sol_s05_even.arrayEmpirical X K (B l K) x) ≤ X.avgMarg H K x := by
  have havg : 0 ≤ X.avgMarg H K x := by
    unfold Setup5.avgMarg
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun z _ => mul_nonneg ((X.blockLaw H K).nonneg z) (Nat.cast_nonneg _))
  by_cases hpos : 0 < X.p.typeBlocks n K ∧ 0 < X.p.typeSegs n K
  · refine le_of_eq ?_
    refine (pi_expect_coord (fun _ : h.hp.Loc => FinProb.pi fun K' : X.Ty =>
      FinProb.pi fun _ : Fin (X.p.typeBlocks n K') => X.blockLaw H K') l
      (fun b => Lane_sol_s05_even.arrayEmpirical X K (b K) x)).trans ?_
    refine (pi_expect_coord (fun K' : X.Ty =>
      FinProb.pi fun _ : Fin (X.p.typeBlocks n K') => X.blockLaw H K') K
      (fun a => Lane_sol_s05_even.arrayEmpirical X K a x)).trans ?_
    exact Lane_sol_s05_even.arrayEmpirical_mean X H K x hpos.1 hpos.2
  · have hzero : ∀ B : Lane_sol_s05_even.CentreArrays X h,
        Lane_sol_s05_even.arrayEmpirical X K (B l K) x = 0 := by
      intro B
      unfold Lane_sol_s05_even.arrayEmpirical
      have hden : X.p.typeBlocks n K * (X.p.q0 * X.p.typeSegs n K) = 0 := by
        rcases Nat.eq_zero_or_pos (X.p.typeBlocks n K) with h0 | h0
        · rw [h0, zero_mul]
        · rcases Nat.eq_zero_or_pos (X.p.typeSegs n K) with h1 | h1
          · rw [h1, mul_zero, mul_zero]
          · exact absurd ⟨h0, h1⟩ hpos
      rw [hden]
      simp
    simp only [hzero, FinProb.expect_const]
    exact havg

/-- The empirical frequency of a label in a selected subtuple is at most `|array|/|subtuple|` times that in
the whole array (the subtuple's blocks are among the array's blocks). -/
theorem selected_tuple_le_array {h : X.HeightChoice5} (ω : X.CΩ h) (v : EvenRole5 n) (c : X.CRef h)
    (x : Fin N) (hM : ∀ j ∈ c.2, (j : ℕ) < X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1)) :
    ((Finset.univ.filter fun e : (Finset.univ.filter fun i : Fin (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1)) =>
        ∃ j ∈ c.2, X.blockIdx _ j = some i) × Fin (X.p.typeSegs n (X.g.evenType (X.p.J n) v.1)) ×
        Fin X.p.q0 => arr ω c.1 (X.g.evenType (X.p.J n) v.1) e.1 e.2.1 e.2.2 = x).card : ℝ) /
      (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) ≤
    (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1) : ℝ) / c.2.card *
      Lane_sol_s05_even.arrayEmpirical X (X.g.evenType (X.p.J n) v.1)
        (arr ω c.1 (X.g.evenType (X.p.J n) v.1)) x := by
  have hcard : (Finset.univ.filter fun i : Fin (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1)) =>
      ∃ j ∈ c.2, X.blockIdx _ j = some i).card = c.2.card :=
    Lane_sol_s05_even.reference_indices_card X (X.g.evenType (X.p.J n) v.1) c.2 hM
  by_cases hk : X.refLen (X.g.evenType (X.p.J n) v.1) c.2 = 0
  · rw [hk]
    simp only [Nat.cast_zero, div_zero]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Lane_sol_s05_even.arrayEmpirical_nonneg X _ _ x)
  · have hc0 : 0 < c.2.card := by
      rcases Nat.eq_zero_or_pos c.2.card with h0 | h0
      · exact absurd (by unfold Setup5.refLen; rw [h0, zero_mul]) hk
      · exact h0
    have hs0 : 0 < X.p.typeSegs n (X.g.evenType (X.p.J n) v.1) := by
      rcases Nat.eq_zero_or_pos (X.p.typeSegs n (X.g.evenType (X.p.J n) v.1)) with h0 | h0
      · exact absurd (by unfold Setup5.refLen; rw [h0, mul_zero, mul_zero]) hk
      · exact h0
    have hh := Lane_sol_s05_even.subtuple_empirical_le_pool
      (I := Fin (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1)))
      (J := Fin (X.p.typeSegs n (X.g.evenType (X.p.J n) v.1)) × Fin X.p.q0)
      (Finset.univ.filter fun i : Fin (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1)) =>
        ∃ j ∈ c.2, X.blockIdx _ j = some i)
      (fun i e => arr ω c.1 (X.g.evenType (X.p.J n) v.1) i e.1 e.2) x (by rw [hcard]; exact hc0)
      (by simp only [Fintype.card_prod, Fintype.card_fin]; exact Nat.mul_pos hs0 X.p.hq0.1)
    simp only [Fintype.card_prod, Fintype.card_fin, hcard] at hh
    rw [Nat.mul_comm (X.p.typeSegs n (X.g.evenType (X.p.J n) v.1)) X.p.q0] at hh
    exact hh

/-- At a low role the reference is the whole low array. -/
theorem ratio_low (v : EvenRole5 n) (hv : X.g.low (X.p.J n) v.1) (M : Finset (Fin X.blockBound))
    (hM : M.card = match (X.g.evenType (X.p.J n) v.1).2.2 with
      | some j => X.p.lowBlocks n j
      | none => X.p.usedBlocks n) :
    (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1) : ℝ) / M.card ≤ 1 := by
  have htype : ∃ j, (X.g.evenType (X.p.J n) v.1).2.2 = some j := by
    simp only [ChunkGeometry5.low] at hv
    exact ⟨⟨X.g.severity v.1, Nat.lt_succ_of_le hv⟩, by simp [ChunkGeometry5.evenType, hv]⟩
  obtain ⟨j, hj⟩ := htype
  rw [hj] at hM
  simp only at hM
  simp only [Params5.typeBlocks, hj, hM]
  exact div_self_le_one _

/-- At a high role the pool/used ratio is `⌈e^{K_h q₀ u_*} k_*/u_*⌉ / (k_*/u_*) ≤ e^{(1 + K_h) k_*}`. -/
theorem ratio_high (v : EvenRole5 n) (hv : ¬ X.g.low (X.p.J n) v.1) (M : Finset (Fin X.blockBound))
    (hM : M.card = match (X.g.evenType (X.p.J n) v.1).2.2 with
      | some j => X.p.lowBlocks n j
      | none => X.p.usedBlocks n) (hm2 : 2 ≤ X.p.m n) :
    (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1) : ℝ) / M.card ≤
      Real.exp ((1 + X.p.Kh) * ((X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) : ℝ)) := by
  have htype : (X.g.evenType (X.p.J n) v.1).2.2 = none := by
    simp only [ChunkGeometry5.low] at hv
    simp [ChunkGeometry5.evenType, hv]
  rw [htype] at hM
  simp only at hM
  simp only [Params5.typeBlocks, htype, hM]
  obtain ⟨_, hk⟩ := Lane_sol_s05_even.high_lengths_positive X.p n hm2
  have hub : 0 < X.p.usedBlocks n := Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hk; omega)
  have hqu : 0 < X.p.q0 * X.p.uStarSeg n :=
    Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hk; omega)
  have hubR : (1 : ℝ) ≤ X.p.usedBlocks n := by exact_mod_cast hub
  have hquR : (1 : ℝ) ≤ (X.p.q0 : ℝ) * X.p.uStarSeg n := by exact_mod_cast hqu
  set a := X.p.Kh * ((X.p.q0 : ℝ) * X.p.uStarSeg n) with ha
  have ha0 : 0 ≤ a := mul_nonneg X.p.hKh.le (by positivity)
  have hpool : (X.p.poolBlocks n : ℝ) ≤ Real.exp a * X.p.usedBlocks n + 1 := by
    unfold Params5.poolBlocks
    exact (Nat.ceil_lt_add_one (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _))).le
  have hea : 1 ≤ Real.exp a := Real.one_le_exp_iff.mpr ha0
  have hratio : (X.p.poolBlocks n : ℝ) / X.p.usedBlocks n ≤ 2 * Real.exp a := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hk' : ((X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) : ℝ) =
      (X.p.q0 : ℝ) * X.p.uStarSeg n * X.p.usedBlocks n := by
    push_cast; ring
  have hexp : 1 + a ≤ (1 + X.p.Kh) * ((X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) : ℝ) := by
    rw [hk', ha]
    have h1 : (X.p.q0 : ℝ) * X.p.uStarSeg n ≤ (X.p.q0 : ℝ) * X.p.uStarSeg n * X.p.usedBlocks n := by
      nlinarith
    nlinarith [X.p.hKh]
  calc
    (X.p.poolBlocks n : ℝ) / X.p.usedBlocks n ≤ 2 * Real.exp a := hratio
    _ ≤ Real.exp 1 * Real.exp a := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = Real.exp (1 + a) := (Real.exp_add 1 a).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexp

/-- The per-center selection mean (05:1220–1240): at fixed arrays the legal selection of `l` has probability at
most `λ/V (3/λ 1_{level 0} + ε)` on the radius-`r` ball, so the selected array's label frequency has mean at
most that times its unselected mean. -/
theorem centre_selection_mean (L : X.CentreLayer5) (H : X.KeyHist) (v : EvenRole5 n) (l : L.ht.hp.Loc)
    (K : X.Ty) (x : Fin N) (U : FinProb Unit) (ε : ℝ) (hlam : 0 < L.ht.hp.lam)
    (hpos : ∀ E : (L.ht.hp.Loc → Bool) → L.ht.hp.EligMap,
      (((L.ht.hp.posLawForced (some l)).prod U).prod L.ht.hp.actLaw).pr (fun ω =>
        L.ht.hp.Legal ω.1.1 (E ω.1.1) (L.ht.hp.domBall (X.sites L.ht) (X.siteOf v) L.ht.hp.Rlong) ∧
          0 < L.ht.hp.height (X.sites L.ht) ω.1.1 ω.2 (E ω.1.1) L.ht.hp.Rlong (X.siteOf v)) ≤ ε) :
    (X.centreLaw L.ht H).expect (fun ω =>
      @ite ℝ (X.selLong (L.elig H) ω v = some l ∧
          L.ht.hp.Legal (pos ω) (L.elig H ω) (L.ht.hp.domBall (X.sites L.ht) (X.siteOf v) L.ht.hp.Rlong))
        (Classical.propDecidable _) (Lane_sol_s05_even.arrayEmpirical X K (arr ω l K) x) 0) ≤
    L.ht.hp.lam / L.ht.hp.V *
      ((if l.2.val = 0 ∧ _root_.hammingDist l.1 (X.siteOf v) ≤ L.ht.hp.r then 3 / L.ht.hp.lam else 0) +
        (if _root_.hammingDist l.1 (X.siteOf v) ≤ L.ht.hp.r then ε else 0)) *
      (Lane_sol_s05_even.centreArrayLaw X L.ht H).expect
        (fun B => Lane_sol_s05_even.arrayEmpirical X K (B l K) x) := by
  have hsite : X.siteOf v ∈ X.sites L.ht := Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  let good : X.CΩ L.ht → Prop := fun ω => X.selLong (L.elig H) ω v = some l ∧
    L.ht.hp.Legal (pos ω) (L.elig H ω) (L.ht.hp.domBall (X.sites L.ht) (X.siteOf v) L.ht.hp.Rlong)
  refine Lane_sol_s05_even.centre_selected_array_mean X L H good
    (fun B => Lane_sol_s05_even.arrayEmpirical X K (B l K) x)
    (fun B => Lane_sol_s05_even.arrayEmpirical_nonneg X K _ x) _ ?_
  intro B
  let Es : (L.ht.hp.Loc → Bool) → L.ht.hp.EligMap := fun P => Lane_sol_s05_even.centreAxesElig X L H P B
  have hgood : ∀ P A T, @ite ℝ (good (Lane_sol_s05_even.centreFromAxes X P A T B))
      (Classical.propDecidable _) 1 0 =
      if L.ht.hp.Legal P (Es P) (L.ht.hp.domBall (X.sites L.ht) (X.siteOf v) L.ht.hp.Rlong) ∧
        L.ht.hp.selection (X.sites L.ht) P A (Es P) T (X.siteOf v) = some l then 1 else 0 := by
    intro P A T
    have he := Lane_sol_s05_even.elig_from_axes X L H P A T B
    simp only [good, Setup5.selLong, he]
    exact if_congr ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩ rfl rfl
  refine le_trans (le_of_eq ?_) (selection_point_bound L.ht.hp hlam (X.sites L.ht) (X.siteOf v) hsite Es
    (fun P j l' hl' => (L.elig_shape H _ (X.siteOf v) j l' hl').2.1) l U ε (hpos Es))
  congr 1
  funext P
  congr 1
  funext A
  congr 1
  funext T
  exact hgood P A T

end
end HypercubeRamsey.Setup5.Lane_opus_s05_d6
