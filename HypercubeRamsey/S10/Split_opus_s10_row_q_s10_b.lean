import HypercubeRamsey.S10.Transfer_sol_s10_1k
import HypercubeRamsey.Tools.CubeGeometry

namespace HypercubeRamsey.Lane_q_s10_b

open OAI.HypercubeRamsey
open scoped BigOperators

/-- Scattered moments bound a retained odd-column failure after normalizing
the column sum by the number of labels. -/
theorem scattered_scaled_column_tail
    {Ω U Y : Type*} [Fintype Ω] [Fintype U] [DecidableEq U] [Nonempty U]
    (P : FinProb Ω) (good : Finset Ω) (row : U → Y → Ω → ℝ)
    (hrow_nonneg : ∀ u y ω, 0 ≤ row u y ω)
    (N : ℕ) (hN : 0 < N) (L : ℝ) (hL : 0 ≤ L)
    (hcap : ∀ u y ω, ω ∈ good → (N : ℝ) * row u y ω ≤ L)
    (near : U → Finset U) (hself : ∀ u, u ∈ near u)
    (f : ℝ) (hnear : ∀ u, ((near u).card : ℝ) ≤ f * Fintype.card U)
    (n : ℕ) (d : Y → U → ℝ) (hd : ∀ y u, 0 ≤ d y u)
    (hjoint : ∀ y m, m ≤ n → ∀ s : Fin m → U,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
        ∑ ω ∈ good, P.w ω * ∏ i, (N : ℝ) * row (s i) y ω ≤ ∏ i, d y (s i))
    (avg : ℝ) (havg : ∀ y,
      (Fintype.card U : ℝ)⁻¹ * ∑ u, d y u ≤ avg)
    (thr : ℝ) (hthr : 0 < thr) :
    ∀ y, P.pr (fun ω => ω ∈ good ∧ thr < ∑ u, row u y ω) ≤
      ((Fintype.card U : ℝ) * (avg + n * f * L) / ((N : ℝ) * thr)) ^ n := by
  classical
  intro y
  let c : ℝ := Fintype.card U
  let t : ℝ := (N : ℝ) * thr / c
  let b : ℝ := c⁻¹ * ∑ u, d y u + n * f * L
  let q : ℝ := avg + n * f * L
  let Z : U → Ω → ℝ := fun u ω => (N : ℝ) * row u y ω
  have hcNat : 0 < Fintype.card U := Fintype.card_pos_iff.mpr ‹Nonempty U›
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast hcNat
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have ht : 0 < t := by positivity
  have hf : 0 ≤ f := by
    obtain ⟨u₀⟩ := ‹Nonempty U›
    have hcard : (1 : ℝ) ≤ ((near u₀).card : ℝ) := by
      have hmem : u₀ ∈ near u₀ := hself u₀
      exact_mod_cast (Finset.card_pos.mpr ⟨u₀, hmem⟩)
    have hprod : (1 : ℝ) ≤ f * c := by
      exact hcard.trans (hnear u₀)
    nlinarith
  have hdsum : 0 ≤ ∑ u, d y u := Finset.sum_nonneg fun u _ => hd y u
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact add_nonneg (mul_nonneg (by positivity) hdsum)
      (mul_nonneg (mul_nonneg (by positivity) hf) hL)
  have hble : b ≤ q := by
    dsimp [b, q]
    exact add_le_add (havg y) le_rfl
  have hq0 : 0 ≤ q := hb0.trans hble
  have hratio : b / t ≤ (c * q) / ((N : ℝ) * thr) := by
    calc
      b / t ≤ q / t := div_le_div_of_nonneg_right hble ht.le
      _ = (c * q) / ((N : ℝ) * thr) := by
        dsimp [t]
        field_simp
        <;> ring
  have hZ : ∀ u ω, 0 ≤ Z u ω := by
    intro u ω
    dsimp [Z]
    exact mul_nonneg (by positivity) (hrow_nonneg u y ω)
  have hcapZ : ∀ u ω, ω ∈ good → Z u ω ≤ L := by
    intro u ω hω
    exact hcap u y ω hω
  have hjointZ : ∀ m, m ≤ n → ∀ s : Fin m → U,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
        ∑ ω ∈ good, P.w ω * ∏ i, Z (s i) ω ≤
          (1 : ℝ) ^ m * ∏ i, d y (s i) := by
    intro m hm s hs
    simpa [Z, one_pow] using hjoint y m hm s hs
  have htail := Lane_sol_s10_1k.scattered_retained_tail P good Z hZ L hL
    hcapZ near hself f hnear n 1 (by norm_num) (d y) (hd y)
    (by
      intro m hm s hs
      simpa [one_pow] using hjointZ m hm s hs)
    t ht
  have hsumZ (ω : Ω) :
      c⁻¹ * ∑ u, Z u ω = ((N : ℝ) * ∑ u, row u y ω) / c := by
    calc
      c⁻¹ * ∑ u, Z u ω = c⁻¹ * ((N : ℝ) * ∑ u, row u y ω) := by
        congr 1
        simp [Z, Finset.mul_sum]
      _ = ((N : ℝ) * ∑ u, row u y ω) / c := by
        rw [div_eq_mul_inv]
        ring
  have hscaled (ω : Ω) :
      thr < ∑ u, row u y ω ↔ t < c⁻¹ * ∑ u, Z u ω := by
    rw [hsumZ]
    dsimp [t]
    rw [div_lt_div_iff_of_pos_right hc]
    constructor
    · intro hlt
      exact mul_lt_mul_of_pos_left hlt hNreal
    · intro hmul
      have hdiv :
          ((N : ℝ) * thr) / (N : ℝ) < ((N : ℝ) * (∑ u, row u y ω)) / (N : ℝ) :=
        (div_lt_div_iff_of_pos_right hNreal).2 hmul
      simpa [mul_div_cancel_left₀, hNreal.ne'] using hdiv
  have hevent :
      (fun ω => ω ∈ good ∧ thr < ∑ u, row u y ω) =
      (fun ω => ω ∈ good ∧ t < c⁻¹ * ∑ u, Z u ω) := by
    funext ω
    exact propext (and_congr_right fun _ => hscaled ω)
  have htail' :
      P.pr (fun ω => ω ∈ good ∧ thr < ∑ u, row u y ω) ≤ (b / t) ^ n := by
    rw [hevent]
    calc
      P.pr (fun ω => ω ∈ good ∧ t < c⁻¹ * ∑ u, Z u ω) ≤
          (1 ^ n * (c⁻¹ * ∑ u, d y u + n * f * L) ^ n) / t ^ n := htail
      _ = (b / t) ^ n := by
        dsimp [b]
        calc
          1 ^ n * (c⁻¹ * ∑ u, d y u + n * f * L) ^ n / t ^ n =
              (c⁻¹ * ∑ u, d y u + n * f * L) ^ n / t ^ n := by simp
          _ = ((c⁻¹ * ∑ u, d y u + n * f * L) / t) ^ n := by rw [← div_pow]
  have hfinal : (b / t) ^ n ≤ (c * q / ((N : ℝ) * thr)) ^ n :=
    pow_le_pow_left₀ (div_nonneg hb0 ht.le) hratio n
  calc
    P.pr (fun ω => ω ∈ good ∧ thr < ∑ u, row u y ω) ≤ (b / t) ^ n := htail'
    _ ≤ (c * q / ((N : ℝ) * thr)) ^ n := hfinal

/-- The independent-group tail estimate for every label at once. -/
theorem independent_group_tail
    {I Y : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (X : ∀ i, Y → Ω i → ℝ)
    (L m θ : ℝ) (hL : 0 < L)
    (hX : ∀ i y ω, 0 ≤ X i y ω ∧ X i y ω ≤ L)
    (hmean : ∀ y, ∑ i, (P i).expect (fun ω => X i y ω) ≤ m) :
    ∀ y, (FinProb.pi P).pr (fun ω => θ ≤ ∑ i, X i y (ω i)) ≤
      Real.exp (((Real.exp 1 - 1) * m - θ) / L) := by
  intro y
  exact Lane_sol_s10_1k.independent_group_column_tail P
    (fun i ω => X i y ω) L m θ hL
    (by intro i ω; exact hX i y ω) (hmean y)

/-- Regroup a finite sum by the value of its group map. -/
theorem grouped_sum_eq
    {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    (grp : B → I) (f : B → ℝ) :
    (∑ i, ∑ b, (if grp b = i then f b else 0)) = ∑ b, f b := by
  classical
  calc
    (∑ i, ∑ b, if grp b = i then f b else 0) =
        ∑ b, ∑ i, if grp b = i then f b else 0 := Finset.sum_comm
    _ = ∑ b, f b := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_eq_single (grp b)]
      · simp
      · intro i hi hne
        simp [hne.symm]
      · simp

/-- Reindex the sum of expected group contributions by their roles. -/
theorem grouped_expect_sum_eq
    {B I C Y : Type*} [Fintype B] [Fintype I] [Fintype C] [Fintype Y] [DecidableEq I]
    (grp : B → I) (P : I → FinProb C) (lab : B → C → FinProb Y) (y : Y) :
    ∑ i, (P i).expect (fun c => ∑ b, if grp b = i then (lab b c).w y else 0) =
      ∑ b, (P (grp b)).expect (fun c => (lab b c).w y) := by
  classical
  have hsingle (b : B) (c : C) :
      ∑ i, (P i).w c * (if grp b = i then (lab b c).w y else 0) =
        (P (grp b)).w c * (lab b c).w y := by
    rw [Finset.sum_eq_single (grp b)]
    · simp
    · intro i hi hne
      have hne' : grp b ≠ i := hne.symm
      simp [hne']
    · simp
  unfold FinProb.expect
  calc
    (∑ i, ∑ c, (P i).w c * ∑ b, if grp b = i then (lab b c).w y else 0) =
        ∑ i, ∑ c, ∑ b, (P i).w c * (if grp b = i then (lab b c).w y else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ b, ∑ c, (P i).w c * (if grp b = i then (lab b c).w y else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ b, ∑ i, ∑ c, (P i).w c * (if grp b = i then (lab b c).w y else 0) :=
      Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ i, (P i).w c * (if grp b = i then (lab b c).w y else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = ∑ b, ∑ c, (P (grp b)).w c * (lab b c).w y := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      exact hsingle b c
    _ = ∑ b, (P (grp b)).expect (fun c => (lab b c).w y) := rfl

/-- A finite union bound under a finite probability law. -/
theorem pr_exists_le_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinProb Ω) (bad : I → Ω → Prop) :
    P.pr (fun ω => ∃ i, bad i ω) ≤ ∑ i, P.pr (bad i) := by
  classical
  unfold FinProb.pr
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : ∃ i, bad i ω
  · rw [ite_eq_left hω]
    obtain ⟨i, hi⟩ := hω
    calc
      P.w ω = (if bad i ω then P.w ω else 0) := by rw [if_pos hi]
      _ ≤ ∑ j, if bad j ω then P.w ω else 0 :=
        Finset.single_le_sum (f := fun j => if bad j ω then P.w ω else 0)
          (fun j _ => by split_ifs <;> simp [P.nonneg ω]) (Finset.mem_univ i)
  · rw [ite_eq_right hω]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [P.nonneg ω]

/-- Event probabilities are monotone under inclusion. -/
theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    {A B : Ω → Prop} (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω <;> simp [hA, hB, P.nonneg ω]

/-- Nonnegativity of probabilities under a finite probability law. -/
theorem pr_nonneg {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    0 ≤ P.pr A := by
  classical
  unfold FinProb.pr
  exact Finset.sum_nonneg fun ω _ => by
    split_ifs <;> simp [P.nonneg ω]

end HypercubeRamsey.Lane_q_s10_b
