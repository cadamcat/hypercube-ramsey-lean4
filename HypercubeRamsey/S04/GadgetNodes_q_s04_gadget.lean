import HypercubeRamsey.S04.CoreLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.Lane_q_s04_gadget

open Classical Filter OAI.HypercubeRamsey
open HypercubeRamsey.S04

private theorem chunkCoords_below_specialNum {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
    (j : Fin (HypercubeRamsey.S04.chunkNum β γ n)) {i : Fin n}
    (hi : i ∈ HypercubeRamsey.S04.chunkCoords β γ n g j) :
    i.val < HypercubeRamsey.S04.specialNum β γ n := by
  classical
  unfold HypercubeRamsey.S04.chunkCoords at hi
  rcases Finset.mem_filter.mp hi with ⟨_, ⟨hlo, hhi⟩⟩
  let G := HypercubeRamsey.S04.gadgetNum β γ n
  let s := HypercubeRamsey.S04.chunkNum β γ n
  let ℓ := HypercubeRamsey.S04.chunkLen β γ n
  have hs : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hgs : g.val * s + j.val + 1 ≤ (g.val + 1) * s := by
    rw [Nat.add_mul, one_mul]
    omega
  have hG : (g.val + 1) * s ≤ G * s := Nat.mul_le_mul_right s (Nat.succ_le_of_lt g.isLt)
  have hblock := Nat.mul_le_mul_right ℓ (hgs.trans hG)
  have hblock' : (g.val * s + j.val) * ℓ + ℓ ≤ G * s * ℓ := by
    simpa [Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Nat.mul_assoc, G, s, ℓ] using hblock
  have hhi' : i.val < (g.val * s + j.val) * ℓ + ℓ := by
    simpa [HypercubeRamsey.S04.chunkStart, G, s, ℓ] using hhi
  have hspec : HypercubeRamsey.S04.specialNum β γ n = G * s * ℓ := by
    simp [HypercubeRamsey.S04.specialNum, G, s, ℓ, Nat.mul_assoc]
  rw [hspec]
  omega

private theorem chunkCount_flip_eq {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
    (j : Fin (HypercubeRamsey.S04.chunkNum β γ n))
    (v : CubeVertex n) (i : Fin n)
    (hi : i ∉ HypercubeRamsey.S04.chunkCoords β γ n g j) :
    HypercubeRamsey.S04.chunkCount β γ n g j (HypercubeRamsey.cubeFlip v i) =
      HypercubeRamsey.S04.chunkCount β γ n g j v := by
  classical
  unfold HypercubeRamsey.S04.chunkCount
  congr 1
  apply Finset.filter_congr
  intro j' hj'
  by_cases hji : j' = i
  · subst j'
    exact False.elim (hi hj')
  · simp [HypercubeRamsey.cubeFlip, Function.update_of_ne hji]

private theorem gadgetOut_flip_eq {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
    (v : CubeVertex n) (i : Fin n)
    (hi : ∀ j : Fin (HypercubeRamsey.S04.chunkNum β γ n),
      i ∉ HypercubeRamsey.S04.chunkCoords β γ n g j) :
    HypercubeRamsey.S04.gadgetOut β γ n g (HypercubeRamsey.cubeFlip v i) =
      HypercubeRamsey.S04.gadgetOut β γ n g v := by
  classical
  have hclip : ∀ j : Fin (HypercubeRamsey.S04.chunkNum β γ n),
      HypercubeRamsey.S04.clipped β γ n g j (HypercubeRamsey.cubeFlip v i) =
        HypercubeRamsey.S04.clipped β γ n g j v := by
    intro j
    simp [HypercubeRamsey.S04.clipped, chunkCount_flip_eq g j v i (hi j)]
  have hfun :
      (fun j : Fin (HypercubeRamsey.S04.chunkNum β γ n) =>
        HypercubeRamsey.S04.clipped β γ n g j (HypercubeRamsey.cubeFlip v i)) =
      (fun j => HypercubeRamsey.S04.clipped β γ n g j v) := by
    funext j
    exact hclip j
  have hsorted : HypercubeRamsey.S04.sortedCounts β γ n g (HypercubeRamsey.cubeFlip v i) =
      HypercubeRamsey.S04.sortedCounts β γ n g v := by
    unfold HypercubeRamsey.S04.sortedCounts
    rw [hfun]
  have hstep : ∀ ab,
      HypercubeRamsey.S04.searchStep β γ n g (HypercubeRamsey.cubeFlip v i) ab =
        HypercubeRamsey.S04.searchStep β γ n g v ab := by
    intro ab
    simp [HypercubeRamsey.S04.searchStep, HypercubeRamsey.S04.rankValue, hsorted]
  have hleaf : HypercubeRamsey.S04.searchLeaf β γ n g (HypercubeRamsey.cubeFlip v i) =
      HypercubeRamsey.S04.searchLeaf β γ n g v := by
    have hfold (L : List ℕ) (ab : ℕ × ℕ) :
        List.foldl (fun ab _ => HypercubeRamsey.S04.searchStep β γ n g
          (HypercubeRamsey.cubeFlip v i) ab) ab L =
        List.foldl (fun ab _ => HypercubeRamsey.S04.searchStep β γ n g v ab) ab L := by
      induction L generalizing ab with
      | nil => rfl
      | cons a L ih => simp [List.foldl_cons, hstep, ih]
    unfold HypercubeRamsey.S04.searchLeaf
    exact hfold _ _
  unfold HypercubeRamsey.S04.gadgetOut
  rw [hleaf]
  simp [hclip]

private theorem sum_eq_sum_fiber_card {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (f : ι → κ) (g : κ → ℝ) :
    (∑ i, g (f i)) =
      ∑ k, ((Finset.univ.filter fun i : ι => f i = k).card : ℝ) * g k := by
  classical
  calc
    (∑ i, g (f i)) = ∑ i, ∑ k, (if f i = k then g k else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
    _ = ∑ k, ∑ i, (if f i = k then g k else 0) := Finset.sum_comm
    _ = ∑ k, ((Finset.univ.filter fun i : ι => f i = k).card : ℝ) * g k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      simp [Finset.sum_const]

private theorem sum_fiber_card_eq_card {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (f : ι → κ) :
    (∑ k, ((Finset.univ.filter fun i : ι => f i = k).card : ℝ)) =
      Fintype.card ι := by
  classical
  have h := sum_eq_sum_fiber_card f (fun _ => (1 : ℝ))
  simpa using h.symm

theorem weightedTag_tail {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : FinProb ι) (α : κ → ℝ) (B K : ℝ)
    (hαsum : ∑ k, α k = 1) (hα : ∀ k, 0 ≤ α k)
    (hwidth : 0 < ∑ k, (α k * B) ^ 2)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ B)
    (hmean : P.expect f ≤ K) (hK : 0 < K) :
    (FinProb.pi (fun _ : κ => P)).pr
      (fun tag : κ → ι => 2 * K < ∑ k, α k * f (tag k)) ≤
        2 * Real.exp (-2 * K ^ 2 / ∑ k, (α k * B) ^ 2) := by
  classical
  let X : κ → ι → ℝ := fun k i => α k * f i
  have hX : ∀ k i, 0 ≤ X k i ∧ X k i ≤ α k * B := by
    intro k i
    constructor
    · exact mul_nonneg (hα k) (hf i).1
    · exact mul_le_mul_of_nonneg_left (hf i).2 (hα k)
  have hwidth' : 0 < ∑ k, (α k * B - 0) ^ 2 := by simpa using hwidth
  have htail := HypercubeRamsey.xChernoff (fun _ : κ => P) X
    (fun _ => 0) (fun k => α k * B) hX hwidth' K hK
  have hmean' : ∑ k, P.expect (X k) ≤ K := by
    calc
      (∑ k, P.expect (X k)) = (∑ k, α k) * P.expect f := by
        simp [X, FinProb.expect_smul, ← Finset.sum_mul]
      _ = P.expect f := by rw [hαsum, one_mul]
      _ ≤ K := hmean
  have hsub : ∀ tag : κ → ι, (2 * K < ∑ k, α k * f (tag k)) →
      K ≤ |(∑ k, X k (tag k)) - ∑ k, P.expect (X k)| := by
    intro tag htag
    have hdiff : K < (∑ k, X k (tag k)) - ∑ k, P.expect (X k) := by
      dsimp [X]
      have : ∑ k, P.expect (X k) ≤ K := hmean'
      linarith
    have hpos : 0 < (∑ k, X k (tag k)) - ∑ k, P.expect (X k) := by linarith
    rw [abs_of_pos hpos]
    linarith
  exact (HypercubeRamsey.S04.pr_mono (FinProb.pi (fun _ : κ => P)) hsub).trans (by simpa using htail)

private theorem pr_exists_le {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (P : FinProb Ω) (A : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i, A i ω) ≤ ∑ i, P.pr (A i) := by
  classical
  have haux (s : Finset ι) :
      P.pr (fun ω => ∃ i ∈ s, A i ω) ≤ ∑ i ∈ s, P.pr (A i) := by
    induction s using Finset.induction_on with
    | empty => simp [FinProb.pr]
    | @insert a s ha ih =>
      have heq : (fun ω => ∃ i ∈ insert a s, A i ω) =
          (fun ω => A a ω ∨ ∃ i ∈ s, A i ω) := by
        funext ω
        simp [ha]
      rw [heq]
      calc
        P.pr (fun ω => A a ω ∨ ∃ i ∈ s, A i ω) ≤
            P.pr (A a) + P.pr (fun ω => ∃ i ∈ s, A i ω) := FinProb.pr_union P _ _
        _ ≤ P.pr (A a) + ∑ i ∈ s, P.pr (A i) := add_le_add le_rfl ih
        _ = ∑ i ∈ insert a s, P.pr (A i) := by rw [Finset.sum_insert ha]
  simpa using haux (Finset.univ : Finset ι)

set_option maxHeartbeats 0 in
theorem tag_exists_bound (β γ K : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hγ : γ < 1) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyFiber β γ n →
      ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
        (M : Menu4 β γ G n N E X Y) (ρ : FinProb M.ι), N ≤ n * 2 ^ n →
        Balanced ρ M.μ M.ν K → ∃ tag : Key β γ n → M.ι, TagBal M tag (2 * K) := by
  let ω := HypercubeRamsey.omega4 β γ
  have hω : 0 < ω := HypercubeRamsey.S04.omega4_pos hβ hγ
  have hγpos : 0 < γ := lt_of_lt_of_le hβ hβγ
  have hpowω : Tendsto (fun n : ℕ => (n : ℝ) ^ ω) atTop atTop :=
    (_root_.tendsto_rpow_atTop hω).comp tendsto_natCast_atTop_atTop
  have hpowγ : Tendsto (fun n : ℕ => (n : ℝ) ^ γ) atTop atTop :=
    (_root_.tendsto_rpow_atTop hγpos).comp tendsto_natCast_atTop_atTop
  have hexpRatio0 : Tendsto (fun x : ℝ => Real.exp x / x ^ (1 / γ)) atTop atTop :=
    _root_.tendsto_exp_div_rpow_atTop _
  have hexpRatioN0 : Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) ^ γ) / ((n : ℝ) ^ γ) ^ (1 / γ)) atTop atTop :=
    hexpRatio0.comp hpowγ
  have hexpRatioN : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) ^ γ) / (n : ℝ)) atTop atTop := by
    apply hexpRatioN0.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hden : ((n : ℝ) ^ γ) ^ (1 / γ) = (n : ℝ) := by
      rw [← Real.rpow_mul hnreal.le]
      have hpow : γ * (1 / γ) = 1 := by field_simp [ne_of_gt hγpos]
      rw [hpow, Real.rpow_one]
    rw [hden]
  have hscaled : Tendsto
      (fun n : ℕ => (2 * K ^ 2 * Real.exp ((n : ℝ) ^ γ)) / (n : ℝ)) atTop atTop := by
    simpa [mul_div_assoc] using
      hexpRatioN.const_mul_atTop (mul_pos (by norm_num) (sq_pos_of_pos hK))
  obtain ⟨nT, hnT⟩ := Filter.eventually_atTop.1 (hscaled.eventually_ge_atTop (10 : ℝ))
  obtain ⟨nω, hnω⟩ := Filter.eventually_atTop.1 (hpowω.eventually_ge_atTop (50 : ℝ))
  obtain ⟨nγ, hnγ⟩ := Filter.eventually_atTop.1 (hpowγ.eventually_ge_atTop (2 : ℝ))
  refine ⟨max nT (max nω (max nγ 3)), ?_⟩
  intro n hn hKF N E G X Y M ρ hN hbal
  have hn3 : 3 ≤ n :=
    (Nat.le_max_right nγ 3).trans
      ((Nat.le_max_right nω (max nγ 3)).trans
        ((Nat.le_max_right nT (max nω (max nγ 3))).trans hn))
  have hnT' : nT ≤ n := (Nat.le_max_left nT (max nω (max nγ 3))).trans hn
  have hnω' : nω ≤ n :=
    (Nat.le_max_left nω (max nγ 3)).trans
      ((Nat.le_max_right nT (max nω (max nγ 3))).trans hn)
  have hnγ' : nγ ≤ n :=
    (Nat.le_max_left nγ 3).trans
      ((Nat.le_max_right nω (max nγ 3)).trans
        ((Nat.le_max_right nT (max nω (max nγ 3))).trans hn))
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnreal1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hq : 2 ≤ (n : ℝ) ^ γ := hnγ n hnγ'
  have hu : 50 ≤ (n : ℝ) ^ ω := hnω n hnω'
  have htailScale : 10 * (n : ℝ) ≤ 2 * K ^ 2 * Real.exp ((n : ℝ) ^ γ) := by
    have h := hnT n hnT'
    have hnpositive : 0 < (n : ℝ) := hnreal
    exact (le_div_iff₀ hnpositive).mp h
  have hι : Nonempty M.ι := by
    by_contra hι
    haveI : IsEmpty M.ι := not_nonempty_iff.mp hι
    have hs : (∑ i, ρ.w i) = 0 := by simp
    rw [ρ.sum_eq_one] at hs
    norm_num at hs
  let i₀ : M.ι := Classical.choice hι
  have hNpos : 0 < N := by
    by_contra hN
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    have hs := (M.μ i₀).sum_eq_one
    simp at hs
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hEvenNonempty : Nonempty (EvenRole n) := by
    let v : CubeVertex n := fun _ => false
    have hv : IsEvenRole v := by simp [HypercubeRamsey.IsEvenRole, v]
    exact ⟨⟨v, hv⟩⟩
  have hOddNonempty : Nonempty (OddRole n) := by
    let v : CubeVertex n := fun _ => false
    have hv : IsEvenRole v := by simp [HypercubeRamsey.IsEvenRole, v]
    let i : Fin n := ⟨0, by omega⟩
    have hodd : ¬ IsEvenRole (HypercubeRamsey.cubeFlip v i) := by
      intro hflip
      exact (HypercubeRamsey.cubeFlip_parity v i).mp hflip hv
    exact ⟨⟨HypercubeRamsey.cubeFlip v i, hodd⟩⟩
  have hCeNat : 0 < Fintype.card (EvenRole n) := Fintype.card_pos_iff.mpr hEvenNonempty
  have hCoNat : 0 < Fintype.card (OddRole n) := Fintype.card_pos_iff.mpr hOddNonempty
  have hCe : 0 < (Fintype.card (EvenRole n) : ℝ) := by exact_mod_cast hCeNat
  have hCo : 0 < (Fintype.card (OddRole n) : ℝ) := by exact_mod_cast hCoNat
  let q : ℝ := (n : ℝ) ^ γ
  let A : ℝ := (n : ℝ) ^ (γ + ω) / 10
  let B : ℝ := Real.exp (2 * q)
  let ε : ℝ := Real.exp (-A)
  have hAeq : A = q * (n : ℝ) ^ ω / 10 := by
    dsimp [A, q]
    rw [Real.rpow_add hnreal]
  have hfactor : 1 ≤ (n : ℝ) ^ ω / 10 - 4 := by nlinarith [hu]
  have hqnonneg : 0 ≤ q := Real.rpow_nonneg hnreal.le _
  have hqA : q ≤ A - 4 * q := by
    have hmul := mul_le_mul_of_nonneg_left hfactor hqnonneg
    rw [hAeq]
    nlinarith
  have hBpos : 0 < B := by positivity
  have hBsq : B ^ 2 = Real.exp (4 * q) := by
    dsimp [B]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  let p : FinProb (Key β γ n → M.ι) := FinProb.pi (fun _ : Key β γ n => ρ)
  let fibE : Key β γ n → Finset (EvenRole n) := fun κ =>
    Finset.univ.filter fun a => key β γ n a.1 = κ
  let fibO : Key β γ n → Finset (OddRole n) := fun κ =>
    Finset.univ.filter fun u => key β γ n u.1 = κ
  let αE : Key β γ n → ℝ := fun κ =>
    (Fintype.card (EvenRole n) : ℝ)⁻¹ * (fibE κ).card
  let αO : Key β γ n → ℝ := fun κ =>
    (Fintype.card (OddRole n) : ℝ)⁻¹ * (fibO κ).card
  have hαESum : ∑ κ, αE κ = 1 := by
    dsimp [αE]
    rw [← Finset.mul_sum]
    have hc := sum_fiber_card_eq_card (fun a : EvenRole n => key β γ n a.1)
    rw [hc]
    field_simp [ne_of_gt hCe]
  have hαOSum : ∑ κ, αO κ = 1 := by
    dsimp [αO]
    rw [← Finset.mul_sum]
    have hc := sum_fiber_card_eq_card (fun u : OddRole n => key β γ n u.1)
    rw [hc]
    field_simp [ne_of_gt hCo]
  have hαENonneg : ∀ κ, 0 ≤ αE κ := by
    intro κ
    dsimp [αE]
    positivity
  have hαONonneg : ∀ κ, 0 ≤ αO κ := by
    intro κ
    dsimp [αO]
    positivity
  have hαELe : ∀ κ, αE κ ≤ ε := by
    intro κ
    have h := (hKF κ).1
    have hExp : Real.exp (-A) =
        Real.exp (-((n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ) / 10)) := by
      congr 1
    have hExp' : Real.exp (-((n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ)) / 10) =
        Real.exp (-((n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ) / 10)) := by
      congr 1
      ring
    have hfiber :
        ((Finset.univ.filter fun a : EvenRole n => key β γ n a.1 = κ).card : ℝ) ≤
          Real.exp (-A) * Fintype.card (EvenRole n) := by
      rw [hExp, ← hExp']
      exact h
    dsimp [αE, fibE]
    have hInv : 0 ≤ (Fintype.card (EvenRole n) : ℝ)⁻¹ := inv_nonneg.mpr hCe.le
    calc
      (Fintype.card (EvenRole n) : ℝ)⁻¹ *
          ((Finset.univ.filter fun a : EvenRole n => key β γ n a.1 = κ).card : ℝ) ≤
        (Fintype.card (EvenRole n) : ℝ)⁻¹ *
          (Real.exp (-((n : ℝ) ^ (γ + ω) / 10)) * Fintype.card (EvenRole n)) :=
            mul_le_mul_of_nonneg_left hfiber hInv
      _ = Real.exp (-((n : ℝ) ^ (γ + ω) / 10)) := by
        field_simp [ne_of_gt hCe]
  have hαOLe : ∀ κ, αO κ ≤ ε := by
    intro κ
    have h := (hKF κ).2
    have hExp : Real.exp (-A) =
        Real.exp (-((n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ) / 10)) := by
      congr 1
    have hExp' : Real.exp (-((n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ)) / 10) =
        Real.exp (-((n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ) / 10)) := by
      congr 1
      ring
    have hfiber :
        ((Finset.univ.filter fun u : OddRole n => key β γ n u.1 = κ).card : ℝ) ≤
          Real.exp (-A) * Fintype.card (OddRole n) := by
      rw [hExp, ← hExp']
      exact h
    dsimp [αO, fibO]
    have hInv : 0 ≤ (Fintype.card (OddRole n) : ℝ)⁻¹ := inv_nonneg.mpr hCo.le
    calc
      (Fintype.card (OddRole n) : ℝ)⁻¹ *
          ((Finset.univ.filter fun u : OddRole n => key β γ n u.1 = κ).card : ℝ) ≤
        (Fintype.card (OddRole n) : ℝ)⁻¹ *
          (Real.exp (-((n : ℝ) ^ (γ + ω) / 10)) * Fintype.card (OddRole n)) :=
            mul_le_mul_of_nonneg_left hfiber hInv
      _ = Real.exp (-((n : ℝ) ^ (γ + ω) / 10)) := by
        field_simp [ne_of_gt hCo]
  have hαSq_le (α : Key β γ n → ℝ) (hsum : ∑ κ, α κ = 1)
      (hnonneg : ∀ κ, 0 ≤ α κ) (hle : ∀ κ, α κ ≤ ε) :
      ∑ κ, (α κ * B) ^ 2 ≤ ε * B ^ 2 := by
    have hsq : ∑ κ, α κ ^ 2 ≤ ε := by
      calc
        ∑ κ, α κ ^ 2 ≤ ∑ κ, ε * α κ := by
          apply Finset.sum_le_sum
          intro κ hκ
          have hprod := mul_nonneg (hnonneg κ) (sub_nonneg.mpr (hle κ))
          nlinarith
        _ = ε * 1 := by rw [← Finset.mul_sum, hsum]
        _ = ε := by ring
    calc
      ∑ κ, (α κ * B) ^ 2 = (∑ κ, α κ ^ 2) * B ^ 2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro κ hκ
        rw [mul_pow]
      _ ≤ ε * B ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg B)
  have hαSq_pos (α : Key β γ n → ℝ) (hsum : ∑ κ, α κ = 1)
      (hnonneg : ∀ κ, 0 ≤ α κ) (hB : 0 < B) :
      0 < ∑ κ, (α κ * B) ^ 2 := by
    have hhas : ∃ κ, 0 < α κ := by
      by_contra h
      push_neg at h
      have hz : ∀ κ, α κ = 0 := by
        intro κ
        exact le_antisymm (h κ) (hnonneg κ)
      have hzero : ∑ κ, α κ = 0 := by simp [hz]
      rw [hsum] at hzero
      norm_num at hzero
    obtain ⟨κ, hκ⟩ := hhas
    have hterm : 0 < (α κ * B) ^ 2 := sq_pos_of_pos (mul_pos hκ hB)
    have hle : (α κ * B) ^ 2 ≤ ∑ j, (α j * B) ^ 2 :=
      Finset.single_le_sum (fun j hj => sq_nonneg (α j * B)) (Finset.mem_univ κ)
    exact hterm.trans_le hle
  have hVarEpos : 0 < ∑ κ, (αE κ * B) ^ 2 :=
    hαSq_pos αE hαESum hαENonneg hBpos
  have hVarOpos : 0 < ∑ κ, (αO κ * B) ^ 2 :=
    hαSq_pos αO hαOSum hαONonneg hBpos
  have hVeq : ε * B ^ 2 = Real.exp (4 * q - A) := by
    dsimp [ε]
    rw [hBsq, ← Real.exp_add]
    congr 1
    ring
  have hVarEle : ∑ κ, (αE κ * B) ^ 2 ≤ Real.exp (4 * q - A) :=
    (hαSq_le αE hαESum hαENonneg hαELe).trans_eq hVeq
  have hVarOle : ∑ κ, (αO κ * B) ^ 2 ≤ Real.exp (4 * q - A) :=
    (hαSq_le αO hαOSum hαONonneg hαOLe).trans_eq hVeq
  have hVpos : 0 < Real.exp (4 * q - A) := Real.exp_pos _
  have hVinv : (Real.exp (4 * q - A))⁻¹ = Real.exp (A - 4 * q) := by
    rw [show 4 * q - A = -(A - 4 * q) by ring, Real.exp_neg, inv_inv]
  have htailFrom (S : ℝ) (hSpos : 0 < S) (hSle : S ≤ Real.exp (4 * q - A)) :
      2 * Real.exp (-2 * K ^ 2 / S) ≤ 2 * Real.exp (-10 * (n : ℝ)) := by
    have hInv : (Real.exp (4 * q - A))⁻¹ ≤ S⁻¹ :=
      (inv_le_inv₀ hVpos hSpos).2 hSle
    have hExpLarge : Real.exp q ≤ S⁻¹ := by
      calc
        Real.exp q ≤ Real.exp (A - 4 * q) := Real.exp_le_exp.mpr hqA
        _ = (Real.exp (4 * q - A))⁻¹ := hVinv.symm
        _ ≤ S⁻¹ := hInv
    have hscale : 10 * (n : ℝ) ≤ 2 * K ^ 2 * S⁻¹ := by
      calc
        10 * (n : ℝ) ≤ 2 * K ^ 2 * Real.exp q := htailScale
        _ ≤ 2 * K ^ 2 * S⁻¹ := mul_le_mul_of_nonneg_left hExpLarge (by positivity)
    apply (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)).2
    apply Real.exp_le_exp.mpr
    rw [div_eq_mul_inv]
    nlinarith
  have hsXbound (i : M.ι) : M.sX i ≤ 2 * q := by
    rcases M.prep i with ⟨_, hsX, _, _, _, _, _, _, _⟩
    have hqQ : 2 ≤ q := by simpa [q] using hq
    calc
      M.sX i ≤ 3 / 2 * (n : ℝ) ^ β := hsX
      _ ≤ 3 / 2 * q := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hnreal1 hβγ) (by norm_num)
      _ ≤ 2 * q := by nlinarith [hqQ]
  have hsYbound (i : M.ι) : M.sY i + 1 ≤ 2 * q := by
    rcases M.prep i with ⟨_, _, _, hsY, _, _, _, _, _⟩
    have hqQ : 2 ≤ q := by simpa [q] using hq
    calc
      M.sY i + 1 ≤ 3 / 2 * q + 1 := by
        simpa [add_comm] using add_le_add_right hsY 1
      _ ≤ 2 * q := by linarith [hqQ]
  have hfEven (x : Fin N) (i : M.ι) :
      0 ≤ (N : ℝ) * (M.μ i).w x ∧ (N : ℝ) * (M.μ i).w x ≤ B := by
    rcases M.prep i with ⟨_, _, _, _, hwidth, _, _, _, _⟩
    constructor
    · exact mul_nonneg (Nat.cast_nonneg _) ((M.μ i).nonneg x)
    · calc
        (N : ℝ) * (M.μ i).w x ≤
            (N : ℝ) * (Real.exp (M.sX i) / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (hwidth x) (Nat.cast_nonneg _)
        _ = Real.exp (M.sX i) := by field_simp [ne_of_gt hNreal]
        _ ≤ B := Real.exp_le_exp.mpr (hsXbound i)
  have hfOdd (y : Fin N) (i : M.ι) :
      0 ≤ (N : ℝ) * (M.ν i).w y ∧ (N : ℝ) * (M.ν i).w y ≤ B := by
    rcases M.prep i with ⟨_, _, _, _, _, hwidth, _, _, _⟩
    constructor
    · exact mul_nonneg (Nat.cast_nonneg _) ((M.ν i).nonneg y)
    · calc
        (N : ℝ) * (M.ν i).w y ≤
            (N : ℝ) * (Real.exp (M.sY i + 1) / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (hwidth y) (Nat.cast_nonneg _)
        _ = Real.exp (M.sY i + 1) := by field_simp [ne_of_gt hNreal]
        _ ≤ B := Real.exp_le_exp.mpr (hsYbound i)
  have hmeanEven (x : Fin N) :
      ρ.expect (fun i => (N : ℝ) * (M.μ i).w x) ≤ K := by
    have hb := hbal.1 x
    unfold FinProb.expect
    calc
      (∑ i, ρ.w i * ((N : ℝ) * (M.μ i).w x)) =
          (N : ℝ) * ∑ i, ρ.w i * (M.μ i).w x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ (N : ℝ) * (K / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = K := by field_simp [ne_of_gt hNreal]
  have hmeanOdd (y : Fin N) :
      ρ.expect (fun i => (N : ℝ) * (M.ν i).w y) ≤ K := by
    have hb := hbal.2 y
    unfold FinProb.expect
    calc
      (∑ i, ρ.w i * ((N : ℝ) * (M.ν i).w y)) =
          (N : ℝ) * ∑ i, ρ.w i * (M.ν i).w y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ (N : ℝ) * (K / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = K := by field_simp [ne_of_gt hNreal]
  let δ : ℝ := 2 * Real.exp (-10 * (n : ℝ))
  have htailE (x : Fin N) : p.pr (fun tag : Key β γ n → M.ι =>
      2 * K < ∑ κ, αE κ * ((N : ℝ) * (M.μ (tag κ)).w x)) ≤ δ := by
    calc
      p.pr (fun tag : Key β γ n → M.ι =>
          2 * K < ∑ κ, αE κ * ((N : ℝ) * (M.μ (tag κ)).w x)) ≤
        2 * Real.exp (-2 * K ^ 2 / ∑ κ, (αE κ * B) ^ 2) := by
          exact weightedTag_tail ρ αE B K hαESum hαENonneg hVarEpos
            (fun i => (N : ℝ) * (M.μ i).w x) (hfEven x) (hmeanEven x) hK
      _ ≤ δ := by
        dsimp [δ]
        exact htailFrom _ hVarEpos hVarEle
  have htailO (y : Fin N) : p.pr (fun tag : Key β γ n → M.ι =>
      2 * K < ∑ κ, αO κ * ((N : ℝ) * (M.ν (tag κ)).w y)) ≤ δ := by
    calc
      p.pr (fun tag : Key β γ n → M.ι =>
          2 * K < ∑ κ, αO κ * ((N : ℝ) * (M.ν (tag κ)).w y)) ≤
        2 * Real.exp (-2 * K ^ 2 / ∑ κ, (αO κ * B) ^ 2) := by
          exact weightedTag_tail ρ αO B K hαOSum hαONonneg hVarOpos
            (fun i => (N : ℝ) * (M.ν i).w y) (hfOdd y) (hmeanOdd y) hK
      _ ≤ δ := by
        dsimp [δ]
        exact htailFrom _ hVarOpos hVarOle
  let badE : Fin N → (Key β γ n → M.ι) → Prop := fun x tag =>
    2 * K < ∑ κ, αE κ * ((N : ℝ) * (M.μ (tag κ)).w x)
  let badO : Fin N → (Key β γ n → M.ι) → Prop := fun y tag =>
    2 * K < ∑ κ, αO κ * ((N : ℝ) * (M.ν (tag κ)).w y)
  let badLabel : Fin N ⊕ Fin N → (Key β γ n → M.ι) → Prop := fun z tag =>
    match z with
    | Sum.inl x => badE x tag
    | Sum.inr y => badO y tag
  let Bad : (Key β γ n → M.ι) → Prop := fun tag => ∃ z, badLabel z tag
  have hsumE : ∑ x : Fin N, p.pr (badE x) ≤ (N : ℝ) * δ := by
    calc
      ∑ x : Fin N, p.pr (badE x) ≤ ∑ _x : Fin N, δ :=
        Finset.sum_le_sum fun x hx => htailE x
      _ = (N : ℝ) * δ := by simp
  have hsumO : ∑ y : Fin N, p.pr (badO y) ≤ (N : ℝ) * δ := by
    calc
      ∑ y : Fin N, p.pr (badO y) ≤ ∑ _y : Fin N, δ :=
        Finset.sum_le_sum fun y hy => htailO y
      _ = (N : ℝ) * δ := by simp
  have hsumBad : p.pr Bad ≤ 2 * (N : ℝ) * δ := by
    calc
      p.pr Bad ≤ ∑ z : Fin N ⊕ Fin N, p.pr (badLabel z) := pr_exists_le p badLabel
      _ = (∑ x : Fin N, p.pr (badE x)) + ∑ y : Fin N, p.pr (badO y) := by
        simp [badLabel, Fintype.sum_sum_type]
      _ ≤ (N : ℝ) * δ + (N : ℝ) * δ := add_le_add hsumE hsumO
      _ = 2 * (N : ℝ) * δ := by ring
  have hNrealUpper : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by exact_mod_cast hN
  have hlog4n : Real.log (4 * (n : ℝ)) ≤ 4 * (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 4 * (n : ℝ))
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))
    linarith
  have hpow2 : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hnumer : 4 * (n : ℝ) * (2 : ℝ) ^ n =
      Real.exp (Real.log (4 * (n : ℝ)) + (n : ℝ) * Real.log 2) := by
    calc
      4 * (n : ℝ) * (2 : ℝ) ^ n =
          Real.exp (Real.log (4 * (n : ℝ))) * Real.exp ((n : ℝ) * Real.log 2) := by
            rw [Real.exp_log (by positivity : 0 < 4 * (n : ℝ)), hpow2]
      _ = Real.exp (Real.log (4 * (n : ℝ)) + (n : ℝ) * Real.log 2) :=
        (Real.exp_add _ _).symm
  have hlogPower : (n : ℝ) * Real.log 2 ≤ (n : ℝ) := by
    calc
      (n : ℝ) * Real.log 2 ≤ (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg n)
      _ = (n : ℝ) := by ring
  have hlogTotal : Real.log (4 * (n : ℝ)) + (n : ℝ) * Real.log 2 ≤ 5 * (n : ℝ) := by
    linarith [hlog4n, hlogPower]
  have hnumLe : 4 * (n : ℝ) * (2 : ℝ) ^ n ≤ Real.exp (5 * (n : ℝ)) := by
    rw [hnumer]
    exact Real.exp_le_exp.mpr hlogTotal
  have hsmall : 4 * (n : ℝ) * (2 : ℝ) ^ n * Real.exp (-10 * (n : ℝ)) < 1 := by
    calc
      4 * (n : ℝ) * (2 : ℝ) ^ n * Real.exp (-10 * (n : ℝ)) ≤
          Real.exp (5 * (n : ℝ)) * Real.exp (-10 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hnumLe (Real.exp_nonneg _)
      _ = Real.exp (-5 * (n : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ < 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_lt_exp.mpr
        have hnpos : 0 < (n : ℝ) := hnreal
        linarith
  have hbadlt : p.pr Bad < 1 := by
    calc
      p.pr Bad ≤ 2 * (N : ℝ) * δ := hsumBad
      _ = 4 * (N : ℝ) * Real.exp (-10 * (n : ℝ)) := by dsimp [δ]; ring
      _ ≤ 4 * (n : ℝ) * (2 : ℝ) ^ n * Real.exp (-10 * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        nlinarith [hNrealUpper]
      _ < 1 := hsmall
  have hgoodprob : p.pr (fun tag => ¬ Bad tag) > 0 := by
    have h := HypercubeRamsey.S04.pr_add_pr_not p Bad
    linarith
  have hgood : ∃ tag : Key β γ n → M.ι, ¬ Bad tag := by
    by_contra h
    push_neg at h
    have hzero : p.pr (fun tag => ¬ Bad tag) = 0 := by
      unfold FinProb.pr
      apply Finset.sum_eq_zero
      intro tag htag
      simp [h tag]
    linarith
  obtain ⟨tag, htag⟩ := hgood
  have hAvgE (tag : Key β γ n → M.ι) (x : Fin N) :
      (Fintype.card (EvenRole n) : ℝ)⁻¹ *
        ∑ a : EvenRole n, (N : ℝ) * (M.μ (tag (key β γ n a.1))).w x =
      ∑ κ, αE κ * ((N : ℝ) * (M.μ (tag κ)).w x) := by
    calc
      (Fintype.card (EvenRole n) : ℝ)⁻¹ *
          ∑ a : EvenRole n, (N : ℝ) * (M.μ (tag (key β γ n a.1))).w x =
        (Fintype.card (EvenRole n) : ℝ)⁻¹ *
          ∑ κ, ((Finset.univ.filter fun a : EvenRole n => key β γ n a.1 = κ).card : ℝ) *
            ((N : ℝ) * (M.μ (tag κ)).w x) := by
          congr 1
          exact sum_eq_sum_fiber_card (fun a : EvenRole n => key β γ n a.1)
            (fun κ => (N : ℝ) * (M.μ (tag κ)).w x)
      _ = ∑ κ, ((Fintype.card (EvenRole n) : ℝ)⁻¹ *
          ((Finset.univ.filter fun a : EvenRole n => key β γ n a.1 = κ).card : ℝ)) *
            ((N : ℝ) * (M.μ (tag κ)).w x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro κ hκ
          ring
      _ = ∑ κ, αE κ * ((N : ℝ) * (M.μ (tag κ)).w x) := by
          apply Finset.sum_congr rfl
          intro κ hκ
          simp [αE, fibE]
  have hAvgO (tag : Key β γ n → M.ι) (y : Fin N) :
      (Fintype.card (OddRole n) : ℝ)⁻¹ *
        ∑ u : OddRole n, (N : ℝ) * (M.ν (tag (key β γ n u.1))).w y =
      ∑ κ, αO κ * ((N : ℝ) * (M.ν (tag κ)).w y) := by
    calc
      (Fintype.card (OddRole n) : ℝ)⁻¹ *
          ∑ u : OddRole n, (N : ℝ) * (M.ν (tag (key β γ n u.1))).w y =
        (Fintype.card (OddRole n) : ℝ)⁻¹ *
          ∑ κ, ((Finset.univ.filter fun u : OddRole n => key β γ n u.1 = κ).card : ℝ) *
            ((N : ℝ) * (M.ν (tag κ)).w y) := by
          congr 1
          exact sum_eq_sum_fiber_card (fun u : OddRole n => key β γ n u.1)
            (fun κ => (N : ℝ) * (M.ν (tag κ)).w y)
      _ = ∑ κ, ((Fintype.card (OddRole n) : ℝ)⁻¹ *
          ((Finset.univ.filter fun u : OddRole n => key β γ n u.1 = κ).card : ℝ)) *
            ((N : ℝ) * (M.ν (tag κ)).w y) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro κ hκ
          ring
      _ = ∑ κ, αO κ * ((N : ℝ) * (M.ν (tag κ)).w y) := by
          apply Finset.sum_congr rfl
          intro κ hκ
          simp [αO, fibO]
  have hgoodE : ∀ x : Fin N,
      (Fintype.card (EvenRole n) : ℝ)⁻¹ *
        ∑ a : EvenRole n, (N : ℝ) * (M.μ (tag (key β γ n a.1))).w x ≤ 2 * K := by
    intro x
    by_contra h
    have hlt : 2 * K <
        (Fintype.card (EvenRole n) : ℝ)⁻¹ *
          ∑ a : EvenRole n, (N : ℝ) * (M.μ (tag (key β γ n a.1))).w x := lt_of_not_ge h
    apply htag
    refine ⟨Sum.inl x, ?_⟩
    dsimp [badLabel, badE]
    rw [← hAvgE tag x]
    exact hlt
  have hgoodO : ∀ y : Fin N,
      (Fintype.card (OddRole n) : ℝ)⁻¹ *
        ∑ u : OddRole n, (N : ℝ) * (M.ν (tag (key β γ n u.1))).w y ≤ 2 * K := by
    intro y
    by_contra h
    have hlt : 2 * K <
        (Fintype.card (OddRole n) : ℝ)⁻¹ *
          ∑ u : OddRole n, (N : ℝ) * (M.ν (tag (key β γ n u.1))).w y := lt_of_not_ge h
    apply htag
    refine ⟨Sum.inr y, ?_⟩
    dsimp [badLabel, badO]
    rw [← hAvgO tag y]
    exact hlt
  refine ⟨tag, ?_⟩
  change (∀ x, (Fintype.card (EvenRole n) : ℝ)⁻¹ *
      ∑ a : EvenRole n, (N : ℝ) * (M.μ (tag (key β γ n a.1))).w x ≤ 2 * K) ∧
    (∀ y, (Fintype.card (OddRole n) : ℝ)⁻¹ *
      ∑ u : OddRole n, (N : ℝ) * (M.ν (tag (key β γ n u.1))).w y ≤ 2 * K)
  exact ⟨hgoodE, hgoodO⟩

private theorem gadgetPower_le_four {β γ : ℝ} (n : ℕ) (hn : 2 ≤ n)
    (hω : 0 < HypercubeRamsey.omega4 β γ) :
    (HypercubeRamsey.S04.gadgetPower β γ n : ℝ) ≤
      4 * (n : ℝ) ^ (2 * HypercubeRamsey.omega4 β γ) := by
  let x : ℝ := (n : ℝ) ^ (2 * HypercubeRamsey.omega4 β γ)
  let q : ℕ := ⌈Real.log x / Real.log 2⌉₊
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hxpos : 0 < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hxone : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_rpow hnreal (by linarith)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : 0 ≤ Real.log x / Real.log 2 := div_nonneg hlogx hlog2.le
  have hq : (q : ℝ) < Real.log x / Real.log 2 + 1 := Nat.ceil_lt_add_one hratio
  have hmaxNat : max 1 q ≤ q + 1 := by omega
  have hmax : (max 1 q : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hmaxNat
  have hbound : (max 1 q : ℝ) ≤ Real.log x / Real.log 2 + 2 := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hbound
  have hcast : (HypercubeRamsey.S04.gadgetPower β γ n : ℝ) =
      Real.rpow 2 (max 1 q : ℝ) := by
    unfold HypercubeRamsey.S04.gadgetPower
    rw [Nat.cast_pow]
    rw [← Real.rpow_natCast]
    congr 1
    simp [Nat.cast_max, q, x]
  have heval : Real.rpow 2 (Real.log x / Real.log 2 + 2) = 4 * x := by
    change (2 : ℝ) ^ (Real.log x / Real.log 2 + 2) = 4 * x
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hmul : Real.log 2 * (Real.log x / Real.log 2 + 2) =
        (Real.log x + Real.log 2) + Real.log 2 := by
      field_simp [ne_of_gt hlog2]
      ring
    rw [hmul, Real.exp_add, Real.exp_add, Real.exp_log hxpos,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  calc
    (HypercubeRamsey.S04.gadgetPower β γ n : ℝ) = Real.rpow 2 (max 1 q : ℝ) := hcast
    _ ≤ Real.rpow 2 (Real.log x / Real.log 2 + 2) := hpow
    _ = 4 * x := heval

private theorem specialNum_le_const {β γ : ℝ} (n : ℕ) (hn : 2 ≤ n)
    (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    (HypercubeRamsey.S04.specialNum β γ n : ℝ) ≤
      16384 * (n : ℝ) ^ (γ + 13 * HypercubeRamsey.omega4 β γ) := by
  let ω := HypercubeRamsey.omega4 β γ
  let G := HypercubeRamsey.S04.gadgetNum β γ n
  let s := HypercubeRamsey.S04.chunkNum β γ n
  let ℓ := HypercubeRamsey.S04.chunkLen β γ n
  have hω : 0 < ω := HypercubeRamsey.S04.omega4_pos hβ hγ
  have hωγ : ω < γ := by
    dsimp [ω, HypercubeRamsey.omega4]
    have hm : min β (1 - γ) ≤ β := min_le_left _ _
    have hb : β / 1000 < β := by nlinarith
    linarith
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hG : (G : ℝ) ≤ (n : ℝ) ^ (γ - ω) := by
    dsimp [G, HypercubeRamsey.S04.gadgetNum, ω]
    exact Nat.floor_le (Real.rpow_nonneg hnreal.le _)
  have hS := gadgetPower_le_four n hn hω
  have hs : (s : ℝ) ≤ (HypercubeRamsey.S04.gadgetPower β γ n : ℝ) := by
    exact_mod_cast (Nat.sub_le (HypercubeRamsey.S04.gadgetPower β γ n) 1)
  have hs' : (s : ℝ) ≤ 4 * (n : ℝ) ^ (2 * ω) := hs.trans hS
  have hnonnegG : 0 ≤ (G : ℝ) := Nat.cast_nonneg _
  have hnonnegs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
  have hprod : (G : ℝ) * (s : ℝ) * (s : ℝ) ^ 6 ≤
      (n : ℝ) ^ (γ - ω) * (4 * (n : ℝ) ^ (2 * ω)) ^ 7 := by
    calc
      (G : ℝ) * (s : ℝ) * (s : ℝ) ^ 6 ≤
          (n : ℝ) ^ (γ - ω) * (s : ℝ) * (s : ℝ) ^ 6 := by
        gcongr
      _ = (n : ℝ) ^ (γ - ω) * (s : ℝ) ^ 7 := by ring
      _ ≤ (n : ℝ) ^ (γ - ω) * (4 * (n : ℝ) ^ (2 * ω)) ^ 7 := by
        gcongr
  have hpow : ((n : ℝ) ^ (2 * ω)) ^ 7 = (n : ℝ) ^ (14 * ω) := by
    rw [Real.rpow_pow_comm hnreal.le (2 * ω) 7]
    rw [← Real.rpow_natCast_mul hnreal.le 7 (2 * ω)]
    congr 1
    ring
  have hproduct : (n : ℝ) ^ (γ - ω) * (4 * (n : ℝ) ^ (2 * ω)) ^ 7 =
      16384 * (n : ℝ) ^ (γ + 13 * ω) := by
    calc
      (n : ℝ) ^ (γ - ω) * (4 * (n : ℝ) ^ (2 * ω)) ^ 7 =
          (n : ℝ) ^ (γ - ω) * (4 ^ 7 * ((n : ℝ) ^ (2 * ω)) ^ 7) := by rw [mul_pow]
      _ = 4 ^ 7 * ((n : ℝ) ^ (γ - ω) * (n : ℝ) ^ (14 * ω)) := by rw [hpow]; ring
      _ = 4 ^ 7 * (n : ℝ) ^ (γ - ω + 14 * ω) := by rw [← Real.rpow_add hnreal]
      _ = 16384 * (n : ℝ) ^ (γ + 13 * ω) := by norm_num; congr 1 <;> ring
  have hspecial : (HypercubeRamsey.S04.specialNum β γ n : ℝ) =
      (G : ℝ) * (s : ℝ) * (s : ℝ) ^ 6 := by
    simp [HypercubeRamsey.S04.specialNum, HypercubeRamsey.S04.chunkLen, G, s, ℓ,
      Nat.cast_mul, Nat.cast_pow, Nat.mul_assoc]
    ring
  rw [hspecial]
  exact hprod.trans_eq hproduct

theorem specialNum_eventually_bound {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (HypercubeRamsey.S04.specialNum β γ n : ℝ) ≤
        (n : ℝ) ^ (γ + 14 * HypercubeRamsey.omega4 β γ) := by
  let ω := HypercubeRamsey.omega4 β γ
  have hω : 0 < ω := HypercubeRamsey.S04.omega4_pos hβ hγ
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ω) atTop atTop :=
    (_root_.tendsto_rpow_atTop hω).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop (16384 : ℝ))
  refine ⟨max n₁ 2, ?_⟩
  intro n hn
  have hnlarge : 16384 ≤ (n : ℝ) ^ ω := hn₁ n (le_trans (Nat.le_max_left _ _) hn)
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hpow_nonneg : 0 ≤ (n : ℝ) ^ (γ + 13 * ω) := Real.rpow_nonneg hnreal.le _
  calc
    (HypercubeRamsey.S04.specialNum β γ n : ℝ) ≤
        16384 * (n : ℝ) ^ (γ + 13 * ω) := specialNum_le_const n hn2 hβ hβγ hγ
    _ ≤ (n : ℝ) ^ ω * (n : ℝ) ^ (γ + 13 * ω) :=
      mul_le_mul_of_nonneg_right hnlarge hpow_nonneg
    _ = (n : ℝ) ^ (γ + 14 * ω) := by
      rw [← Real.rpow_add hnreal]
      congr 1
      ring

theorem keyLocal_le_specialNum {β γ : ℝ} (n : ℕ) :
    ∀ v : CubeVertex n,
      ((Finset.univ.filter fun i : Fin n =>
        HypercubeRamsey.S04.key β γ n (HypercubeRamsey.cubeFlip v i) ≠
          HypercubeRamsey.S04.key β γ n v).card : ℝ) ≤
        (HypercubeRamsey.S04.specialNum β γ n : ℝ) := by
  classical
  intro v
  let S : Finset (Fin n) := Finset.univ.filter fun i => i.val < HypercubeRamsey.S04.specialNum β γ n
  have hsub : (Finset.univ.filter fun i : Fin n =>
      HypercubeRamsey.S04.key β γ n (HypercubeRamsey.cubeFlip v i) ≠
        HypercubeRamsey.S04.key β γ n v) ⊆ S := by
    intro i hi
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hge
    have hnot : ∀ g : Fin (HypercubeRamsey.S04.gadgetNum β γ n),
        ∀ j : Fin (HypercubeRamsey.S04.chunkNum β γ n),
          i ∉ HypercubeRamsey.S04.chunkCoords β γ n g j := by
      intro g j hmem
      have hlt := chunkCoords_below_specialNum g j hmem
      omega
    have hkey : HypercubeRamsey.S04.key β γ n (HypercubeRamsey.cubeFlip v i) =
        HypercubeRamsey.S04.key β γ n v := by
      funext g
      exact gadgetOut_flip_eq g v i (hnot g)
    have hneq : HypercubeRamsey.S04.key β γ n (HypercubeRamsey.cubeFlip v i) ≠
        HypercubeRamsey.S04.key β γ n v := (Finset.mem_filter.mp hi).2
    exact hneq hkey
  have hcard : S.card ≤ HypercubeRamsey.S04.specialNum β γ n := by
    calc
      S.card = Fintype.card {i : Fin n // i ∈ S} := by simp
      _ ≤ Fintype.card (Fin (HypercubeRamsey.S04.specialNum β γ n)) :=
        Fintype.card_le_of_injective
          (fun i => (⟨i.1.val, (Finset.mem_filter.mp i.2).2⟩ : Fin (HypercubeRamsey.S04.specialNum β γ n)))
          (by
            intro a b h
            apply Subtype.ext
            apply Fin.ext
            simpa using congrArg Fin.val h)
      _ = HypercubeRamsey.S04.specialNum β γ n := Fintype.card_fin _
  have hle := Finset.card_le_card hsub
  exact_mod_cast hle.trans hcard

end HypercubeRamsey.Lane_q_s04_gadget
