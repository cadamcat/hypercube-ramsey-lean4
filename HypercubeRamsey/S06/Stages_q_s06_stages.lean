import HypercubeRamsey.S06.Defs
import HypercubeRamsey.S03.ConditionalAvoidance

namespace HypercubeRamsey.Lane_q_s06_stages

open Classical
open HypercubeRamsey.S06

theorem restrictOr6_weight_of_pos {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) (ω₀ ω : Ω) (hA : 0 < P.pr A) :
    (restrictOr6 P A ω₀).w ω = (if A ω then P.w ω else 0) / P.pr A := by
  classical
  have hsum : (∑ ω, max 0 (if A ω then P.w ω else 0)) = P.pr A := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : A x
    · simp [h, max_eq_right (P.nonneg x)]
    · simp [h]
  have hmax : ∀ x, max 0 (if A x then P.w x else 0) = if A x then P.w x else 0 := by
    intro x
    split_ifs <;> simp [P.nonneg]
  unfold restrictOr6
  have hpos : 0 < ∑ x, max 0 (if A x then P.w x else 0) := by
    rw [hsum]
    exact hA
  rw [normalize6, dif_pos hpos]
  change max 0 (if A ω then P.w ω else 0) /
      (∑ x, max 0 (if A x then P.w x else 0)) =
    (if A ω then P.w ω else 0) / P.pr A
  rw [hmax ω, hsum]

theorem restrictOr6_support_of_pos {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) (ω₀ ω : Ω) (hA : 0 < P.pr A)
    (hω : (restrictOr6 P A ω₀).w ω ≠ 0) : A ω ∧ P.w ω ≠ 0 := by
  rw [restrictOr6_weight_of_pos P A ω₀ ω hA] at hω
  constructor
  · by_contra h
    simp [h] at hω
  · by_contra h
    have hnum : (if A ω then P.w ω else 0) = 0 := by
      split_ifs with hAω
      · exact h
      · rfl
    rw [hnum] at hω
    simp at hω

theorem pi_support_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (ω : ∀ i, Ω i) (hω : (FinProb.pi P).w ω ≠ 0) :
    ∀ i, (P i).w (ω i) ≠ 0 := by
  classical
  have hprod : (∏ i, (P i).w (ω i)) ≠ 0 := by
    simpa [FinProb.pi] using hω
  intro i
  exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)

theorem bind_support_factors {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (ab : α × β)
    (hab : (FinProb.bind P K).w ab ≠ 0) : P.w ab.1 ≠ 0 ∧ (K ab.1).w ab.2 ≠ 0 := by
  exact mul_ne_zero_iff.mp (by simpa [FinProb.bind] using hab)

theorem pr_congr {Ω : Type*} [Fintype Ω] (P : FinProb Ω) {A B : Ω → Prop}
    (hAB : ∀ ω, A ω ↔ B ω) : P.pr A = P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hA : A ω
  · have hB := (hAB ω).mp hA
    simp [hA, hB]
  · have hB : ¬ B ω := fun h => hA ((hAB ω).mpr h)
    simp [hA, hB]

theorem pr_nonneg {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    0 ≤ P.pr A := by
  classical
  unfold FinProb.pr
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs
  · exact P.nonneg ω
  · exact le_rfl

theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω) {A B : Ω → Prop}
    (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω
    · simpa [hA, hB] using P.nonneg ω
    · simp [hA, hB]

private noncomputable def avoidEventFilter {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I]
    (E : I → Finset Ω) : Finset Ω :=
  @Finset.filter Ω (fun ω => ∀ i ∈ (Finset.univ : Finset I), ω ∉ E i)
    (fun ω => Classical.propDecidable _) Finset.univ

theorem avoid_mass_eq_pr {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [DecidableEq I] (P : FinProb Ω) (E : I → Finset Ω) :
    LocalLemma.mass P.w (LocalLemma.avoid E Finset.univ) =
      P.pr (fun ω => ∀ i ∈ (Finset.univ : Finset I), ω ∉ E i) := by
  classical
  let A : Ω → Prop := fun ω => ∀ i ∈ (Finset.univ : Finset I), ω ∉ E i
  have hfilter : LocalLemma.avoid E Finset.univ = avoidEventFilter E := by
    unfold LocalLemma.avoid avoidEventFilter
    exact (Finset.filter_congr_decidable Finset.univ A
      (fun ω => Classical.propDecidable (A ω))).symm
  calc
    LocalLemma.mass P.w (LocalLemma.avoid E Finset.univ) =
        (avoidEventFilter E).sum P.w := by
          unfold LocalLemma.mass
          rw [hfilter]
    _ = P.pr A := by
      symm
      simp [FinProb.pr, A, avoidEventFilter, Finset.sum_filter]

theorem bind_pr {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (A : α → β → Prop) :
    (FinProb.bind P K).pr (fun ab => A ab.1 ab.2) =
      P.expect (fun a => (K a).pr (A a)) := by
  classical
  simp only [FinProb.pr, FinProb.bind, FinProb.expect, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : A a b <;> simp [h, mul_comm]

theorem pr_exists_finset_le {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] (P : FinProb Ω) (S : Finset ι) (A : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i ∈ S, A i ω) ≤ ∑ i ∈ S, P.pr (A i) := by
  classical
  letI : DecidablePred (fun ω => ∃ i ∈ S, A i ω) :=
    fun ω => Classical.propDecidable (∃ i ∈ S, A i ω)
  have hpr : P.pr (fun ω => ∃ i ∈ S, A i ω) =
      ∑ ω, if (∃ i ∈ S, A i ω) then P.w ω else 0 := rfl
  rw [hpr]
  calc
    (∑ ω, if ∃ i ∈ S, A i ω then P.w ω else 0) ≤
        ∑ ω, ∑ i ∈ S, if A i ω then P.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hex : ∃ i ∈ S, A i ω
      · obtain ⟨i, hiS, hiA⟩ := hex
        calc
          (if ∃ i ∈ S, A i ω then P.w ω else 0) = P.w ω := if_pos ⟨i, hiS, hiA⟩
          _ ≤ ∑ i ∈ S, if A i ω then P.w ω else 0 :=
            calc
              P.w ω = (if A i ω then P.w ω else 0) := (if_pos hiA).symm
              _ ≤ ∑ j ∈ S, if A j ω then P.w ω else 0 :=
                Finset.single_le_sum (f := fun j : ι => if A j ω then P.w ω else 0) (a := i)
                  (fun j hj => by
                    split_ifs
                    · exact P.nonneg ω
                    · exact le_rfl) hiS
      · simp only [if_neg hex]
        exact Finset.sum_nonneg fun i hi => by
          split_ifs
          · exact P.nonneg ω
          · exact le_rfl
    _ = ∑ i ∈ S, (∑ ω, if A i ω then P.w ω else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ S, P.pr (A i) := by simp [FinProb.pr]

theorem pr_exists_shape_le {Ω I Sh : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    [Fintype Sh] [DecidableEq Sh] (P : FinProb Ω) (S : Finset I) (shape : I → Sh)
    (F : Ω → I → ℝ) (t : ℝ)
    (hshape : ∀ i j, shape i = shape j → ∀ ω, F ω i = F ω j) :
    P.pr (fun ω => ∃ i ∈ S, t ≤ F ω i) ≤
      ∑ s : {s // s ∈ S.image shape}, P.pr (fun ω => t ≤ F ω (Classical.choose (Finset.mem_image.mp s.2))) := by
  classical
  let rep : {s // s ∈ S.image shape} → I := fun s => Classical.choose (Finset.mem_image.mp s.2)
  have hrep : ∀ s : {s // s ∈ S.image shape}, rep s ∈ S ∧ shape (rep s) = s.1 := by
    intro s
    exact Classical.choose_spec (Finset.mem_image.mp s.2)
  have hsub : ∀ ω, (∃ i ∈ S, t ≤ F ω i) →
      ∃ s : {s // s ∈ S.image shape}, t ≤ F ω (rep s) := by
    intro ω hω
    obtain ⟨i, hiS, hiF⟩ := hω
    let s : {s // s ∈ S.image shape} := ⟨shape i, Finset.mem_image.mpr ⟨i, hiS, rfl⟩⟩
    refine ⟨s, ?_⟩
    have hs : shape i = shape (rep s) := by
      calc
        shape i = s.1 := rfl
        _ = shape (rep s) := (hrep s).2.symm
    have hF := hshape i (rep s) hs ω
    exact hiF.trans_eq hF
  calc
    P.pr (fun ω => ∃ i ∈ S, t ≤ F ω i) ≤
        P.pr (fun ω => ∃ s : {s // s ∈ S.image shape}, t ≤ F ω (rep s)) :=
      pr_mono P hsub
    _ ≤ ∑ s : {s // s ∈ S.image shape}, P.pr (fun ω => t ≤ F ω (rep s)) := by
      simpa using pr_exists_finset_le P (Finset.univ : Finset {s // s ∈ S.image shape})
        (fun s ω => t ≤ F ω (rep s))

noncomputable def chooseImageRep {I Sh : Type*} [DecidableEq Sh] [Inhabited I]
    (S : Finset I) (shape : I → Sh) (s : Sh) : I :=
  if hs : s ∈ S.image shape then Classical.choose (Finset.mem_image.mp hs) else default

theorem chooseImageRep_spec {I Sh : Type*} [DecidableEq Sh] [Inhabited I]
    (S : Finset I) (shape : I → Sh) {s : Sh} (hs : s ∈ S.image shape) :
    chooseImageRep S shape s ∈ S ∧ shape (chooseImageRep S shape s) = s := by
  classical
  unfold chooseImageRep
  rw [dif_pos hs]
  exact Classical.choose_spec (Finset.mem_image.mp hs)

theorem pr_exists_shape_sum {Ω I Sh : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    [Fintype Sh] [DecidableEq Sh] [Inhabited I]
    (P : FinProb Ω) (S : Finset I) (shape : I → Sh) (F : Ω → I → ℝ) (t : ℝ)
    (hshape : ∀ i j, shape i = shape j → ∀ ω, F ω i = F ω j) :
    P.pr (fun ω => ∃ i ∈ S, t ≤ F ω i) ≤
      ∑ s ∈ S.image shape, P.pr (fun ω => t ≤ F ω (chooseImageRep S shape s)) := by
  classical
  have hsub : ∀ ω, (∃ i ∈ S, t ≤ F ω i) →
      ∃ s ∈ S.image shape, t ≤ F ω (chooseImageRep S shape s) := by
    intro ω hω
    obtain ⟨i, hiS, hiF⟩ := hω
    have hmem : shape i ∈ S.image shape := Finset.mem_image.mpr ⟨i, hiS, rfl⟩
    have hrep := chooseImageRep_spec S shape hmem
    have heq : shape i = shape (chooseImageRep S shape (shape i)) := hrep.2.symm
    have hF := hshape i (chooseImageRep S shape (shape i)) heq ω
    exact ⟨shape i, hmem, hiF.trans_eq hF⟩
  calc
    P.pr (fun ω => ∃ i ∈ S, t ≤ F ω i) ≤
        P.pr (fun ω => ∃ s ∈ S.image shape, t ≤ F ω (chooseImageRep S shape s)) :=
      pr_mono P hsub
    _ ≤ ∑ s ∈ S.image shape, P.pr (fun ω => t ≤ F ω (chooseImageRep S shape s)) :=
      pr_exists_finset_le P (S.image shape)
        (fun s ω => t ≤ F ω (chooseImageRep S shape s))

open Filter

theorem eventually_const_mul_nat_rpow_neg_lt {a c b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ n : ℕ in Filter.atTop, c * (n : ℝ) ^ (-a) < b := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-a)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun _ : ℕ => c) Filter.atTop (nhds c) := tendsto_const_nhds
  have hlim : Tendsto (fun n : ℕ => c * (n : ℝ) ^ (-a)) Filter.atTop (nhds 0) :=
    by simpa using hconst.mul hpow
  filter_upwards [Metric.tendsto_nhds.1 hlim b hb] with n hn
  have habs : |c * (n : ℝ) ^ (-a)| < b := by simpa [Real.dist_eq] using hn
  exact (abs_lt.mp habs).2

theorem eventually_nat_ceil_rpow_add_two_le_double {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((⌈(n : ℝ) ^ a⌉₊ : ℝ) + 2) ≤ (n : ℝ) ^ (2 * a) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ a) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, 4 ≤ (n : ℝ) ^ a :=
    hpow.eventually_ge_atTop 4
  filter_upwards [hlarge] with n hn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg hn0 a)).le
  have hquad : (n : ℝ) ^ a + 3 ≤ ((n : ℝ) ^ a) ^ 2 := by nlinarith
  have hpowEq : (n : ℝ) ^ (2 * a) = ((n : ℝ) ^ a) ^ 2 := by
    rw [show 2 * a = a * 2 by ring, Real.rpow_mul hn0 a 2]
    exact Real.rpow_natCast ((n : ℝ) ^ a) 2
  calc
    ((⌈(n : ℝ) ^ a⌉₊ : ℝ) + 2) ≤ (n : ℝ) ^ a + 3 := by linarith
    _ ≤ ((n : ℝ) ^ a) ^ 2 := hquad
    _ = (n : ℝ) ^ (2 * a) := hpowEq.symm

theorem eventually_T₆_le_J₆ :
    ∀ᶠ m : ℕ in Filter.atTop, T₆ m ≤ J₆ m := by
  have hpow : Tendsto (fun m : ℕ => (m : ℝ) ^ (1 / 1000 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1000)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually_ge_atTop 2] with m hm
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  let x : ℝ := (m : ℝ) ^ (1 / 1000 : ℝ)
  have hpow40 : (m : ℝ) ^ (1 / 25 : ℝ) = x ^ 40 := by
    calc
      (m : ℝ) ^ (1 / 25 : ℝ) = (m : ℝ) ^ ((1 / 1000 : ℝ) * 40) := by congr 1 <;> norm_num
      _ = ((m : ℝ) ^ (1 / 1000 : ℝ)) ^ (40 : ℝ) :=
        Real.rpow_mul hm0 (1 / 1000 : ℝ) 40
      _ = x ^ 40 := by
        simpa [x] using Real.rpow_natCast ((m : ℝ) ^ (1 / 1000 : ℝ)) 40
  have hx2 : x + 1 ≤ x ^ 2 := by dsimp [x] at *; nlinarith
  have hx40 : x ^ 2 ≤ x ^ 40 :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ x) (by norm_num : 2 ≤ 40)
  have hT : (T₆ m : ℝ) ≤ x + 1 := by
    dsimp [T₆, x]
    exact (Nat.ceil_lt_add_one (Real.rpow_nonneg hm0 _)).le
  have hTy : (T₆ m : ℝ) ≤ (m : ℝ) ^ (1 / 25 : ℝ) := by
    rw [hpow40]
    exact hT.trans (hx2.trans hx40)
  have hfloor : T₆ m ≤ ⌊(m : ℝ) ^ (1 / 25 : ℝ)⌋₊ :=
    (Nat.le_floor_iff (Real.rpow_nonneg hm0 _)).2 hTy
  simpa [J₆] using hfloor

theorem m₆_nat_tendsto_atTop (p₀ : ℝ) (hp₀ : 0 < p₀) :
    Tendsto (fun n : ℕ => m₆ p₀ n) Filter.atTop Filter.atTop := by
  have hα : 0 < α₆ p₀ := lt_min (by norm_num) (by linarith)
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ α₆ p₀) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  have hceil : Tendsto (fun x : ℝ => Nat.ceil x) Filter.atTop Filter.atTop :=
    (Nat.ceil_mono (R := ℝ)).tendsto_atTop_atTop
      (fun b : ℕ => ⟨(b : ℝ), by simp⟩)
  have hceilPow : Tendsto (fun n : ℕ => Nat.ceil ((n : ℝ) ^ α₆ p₀))
      Filter.atTop Filter.atTop := hceil.comp hpow
  simpa [m₆] using hceilPow

theorem m₆_tendsto_atTop (p₀ : ℝ) (hp₀ : 0 < p₀) :
    Tendsto (fun n : ℕ => (m₆ p₀ n : ℝ)) Filter.atTop Filter.atTop := by
  exact (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop).comp
      (m₆_nat_tendsto_atTop p₀ hp₀)

end HypercubeRamsey.Lane_q_s06_stages
