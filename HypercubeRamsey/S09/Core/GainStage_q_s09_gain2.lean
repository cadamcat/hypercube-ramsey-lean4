import HypercubeRamsey.S09.Core.Experiment
import HypercubeRamsey.Tools.SignedTest
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.Tools.Finner

/-!
Lane-local analytic and finite-probability helpers for q-s09-gain2.
-/

namespace HypercubeRamsey.Lane_q_s09_gain2

open Classical Filter
open scoped BigOperators Topology

private theorem finprob_ext {α : Type*} [Fintype α] {P Q : FinProb α}
    (h : ∀ x, P.w x = Q.w x) : P = Q := by
  cases P with
  | mk pw hp hs =>
    cases Q with
    | mk qw hq hst =>
      have hw : pw = qw := funext h
      subst qw
      rfl

theorem pi_pr_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (i : ι) (o : Ω i) :
    (FinProb.pi P).pr (fun ω => ω i = o) = (P i).w o := by
  classical
  let S : Finset ι := {i}
  let J := {j // j ∈ S}
  letI : Unique J := ⟨⟨i, by simp [S]⟩, fun j => by
    apply Subtype.ext
    exact Finset.mem_singleton.mp j.2⟩
  let j₀ : J := default
  let f : (∀ j : {j // j ∈ S}, Ω j.1) → ℝ := fun x => if x j₀ = o then 1 else 0
  have hm := FinProb.pi_marginal_expect P S f
  have hleft : (FinProb.pi P).expect (fun ω => if ω i = o then 1 else 0) =
      (FinProb.pi P).pr (fun ω => ω i = o) := by
    simp [FinProb.expect, FinProb.pr, FinProb.pi]
  have hmid : (FinProb.pi P).expect (fun ω => if ω i = o then 1 else 0) =
      (FinProb.pi P).expect (fun ω => f (fun j => ω j.1)) := by
    simpa [f, j₀, S, J] using hm
  have hright :
      (FinProb.pi (fun j : {j // j ∈ S} => P j.1)).expect f = (P i).w o := by
    let e : (∀ j : J, Ω j.1) ≃ Ω i := Equiv.piUnique (fun j : J => Ω j.1)
    change (∑ x : (∀ j : J, Ω j.1),
      (∏ j : J, (P j.1).w (x j)) * f x) = (P i).w o
    rw [← Equiv.sum_comp e.symm]
    simp only [e, Equiv.piUnique_apply, f, j₀, S, J, mul_ite, mul_one, mul_zero]
    simpa using (Finset.sum_ite_eq' Finset.univ o (fun x => (P i).w x))
  calc
    (FinProb.pi P).pr (fun ω => ω i = o) =
        (FinProb.pi P).expect (fun ω => if ω i = o then 1 else 0) := hleft.symm
    _ = (FinProb.pi P).expect (fun ω => f (fun j => ω j.1)) := hmid
    _ = (FinProb.pi (fun j : {j // j ∈ S} => P j.1)).expect f := hm
    _ = (P i).w o := hright

theorem tendsto_nat_rpow_exp_neg_rpow {s u c : ℝ} (hu : 0 < u) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ s * Real.exp (-c * (n : ℝ) ^ u)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) ^ u) atTop atTop :=
    (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop
  have hbase :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / u) c hc).comp hn
  apply Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hpow : (n : ℝ) ^ s = ((n : ℝ) ^ u) ^ (s / u) := by
    rw [← Real.rpow_mul hnR.le]
    congr 1
    field_simp [ne_of_gt hu]
  change ((n : ℝ) ^ u) ^ (s / u) * Real.exp (-c * (n : ℝ) ^ u) =
    (n : ℝ) ^ s * Real.exp (-c * (n : ℝ) ^ u)
  rw [← hpow]

theorem pr_or_le {Ω : Type*} [Fintype Ω] (Q : FinProb Ω) (A B : Ω → Prop) :
    Q.pr (fun ω => A ω ∨ B ω) ≤ Q.pr A + Q.pr B :=
  FinProb.pr_union_le Q A B

theorem pr_or3_le {Ω : Type*} [Fintype Ω] (Q : FinProb Ω)
    (A B C : Ω → Prop) :
    Q.pr (fun ω => A ω ∨ B ω ∨ C ω) ≤ Q.pr A + Q.pr B + Q.pr C := by
  calc
    Q.pr (fun ω => A ω ∨ B ω ∨ C ω) ≤
        Q.pr (fun ω => A ω ∨ B ω) + Q.pr C := by
          have h := pr_or_le Q (fun ω => A ω ∨ B ω) C
          simpa [or_assoc] using h
    _ ≤ Q.pr A + Q.pr B + Q.pr C := by
      linarith [pr_or_le Q A B]

private theorem power_ratio (n : ℕ) (hn : 1 ≤ n) (a b d : ℝ) :
    (n : ℝ) ^ a * ((n : ℝ) ^ (-b)) ^ 2 / ((n : ℝ) ^ (-d) / 2) =
      2 * (n : ℝ) ^ (a + d - 2 * b) := by
  have hx : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsq : ((n : ℝ) ^ (-b)) ^ 2 = (n : ℝ) ^ (-2 * b) := by
    rw [← Real.rpow_mul_natCast hx.le (-b) 2]
    congr 1
    ring
  have hden : (n : ℝ) ^ (-d) = ((n : ℝ) ^ d)⁻¹ := Real.rpow_neg hx.le d
  calc
    (n : ℝ) ^ a * ((n : ℝ) ^ (-b)) ^ 2 / ((n : ℝ) ^ (-d) / 2) =
        2 * (n : ℝ) ^ a * (n : ℝ) ^ (-2 * b) * (n : ℝ) ^ d := by
          rw [hsq, hden]
          have hpow : (n : ℝ) ^ d ≠ 0 := (Real.rpow_pos_of_pos hx d).ne'
          field_simp [hpow]
          <;> ring
    _ = 2 * ((n : ℝ) ^ a * (n : ℝ) ^ (-2 * b) * (n : ℝ) ^ d) := by ring
    _ = 2 * ((n : ℝ) ^ (a + (-2 * b)) * (n : ℝ) ^ d) := by
          rw [← Real.rpow_add hx a (-2 * b)]
    _ = 2 * (n : ℝ) ^ (a + (-2 * b) + d) := by
          rw [← Real.rpow_add hx (a + (-2 * b)) d]
    _ = 2 * (n : ℝ) ^ (a + d - 2 * b) := by congr 2 <;> ring

theorem rowDeg_restrictOr_hit_formula {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (A : Finset (Fin N)) (w x : Fin N)
    (hA : ∀ y, y ∈ A ↔ Hits E G w y)
    (hmass : 0 < ∑ y ∈ A, μ.w y) :
    rowDeg E G x (restrictOr9 μ A) =
      (∑ y, μ.w y * (hitInd9 E G w y * hitInd9 E G x y)) /
        (∑ y ∈ A, μ.w y) := by
  classical
  have hrestrict : restrictOr9 μ A = μ.restrict A hmass := by
    simp [restrictOr9, hmass]
  rw [hrestrict]
  unfold rowDeg Law.restrict
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hw : Hits E G w y
  · have hmem : y ∈ A := (hA y).2 hw
    by_cases hx : Hits E G x y <;> simp [hitInd9, hmem, hw, hx] <;> ring
  · have hmem : y ∉ A := fun hyA => hw ((hA y).1 hyA)
    simp [hitInd9, hmem, hw]

theorem restrictOr_hit_mass_eq_rowDeg {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (A : Finset (Fin N)) (w : Fin N)
    (hA : ∀ y, y ∈ A ↔ Hits E G w y) :
    (∑ y ∈ A, μ.w y) = rowDeg E G w μ := by
  classical
  have hset : A = Finset.univ.filter (fun y : Fin N => Hits E G w y) := by
    ext y
    simp [(hA y)]
  rw [hset, Finset.sum_filter]
  simp [rowDeg]

theorem rowDeg_restrictOr_hit_delta {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (A : Finset (Fin N)) (w x : Fin N)
    (hA : ∀ y, y ∈ A ↔ Hits E G w y)
    (hmass : 0 < ∑ y ∈ A, μ.w y) :
    |rowDeg E G x (restrictOr9 μ A) - rowDeg E G x μ| =
      |((∑ y, μ.w y * (hitInd9 E G w y * hitInd9 E G x y)) -
        rowDeg E G w μ * rowDeg E G x μ) / rowDeg E G w μ| := by
  have hmassEq := restrictOr_hit_mass_eq_rowDeg E G μ A w hA
  have hdenpos : 0 < rowDeg E G w μ := by rw [← hmassEq]; exact hmass
  have hformula := rowDeg_restrictOr_hit_formula E G μ A w x hA hmass
  rw [hmassEq] at hformula
  have hnum :
      rowDeg E G x (restrictOr9 μ A) =
        (∑ y, μ.w y * (hitInd9 E G w y * hitInd9 E G x y)) /
          rowDeg E G w μ := hformula
  rw [hnum]
  congr 1
  field_simp [hdenpos.ne']
  <;> ring

private theorem list_take_succ_eq_append_of_getElem? {α : Type*} (l : List α) (k : ℕ) (c : α)
    (h : l[k]? = some c) : l.take (k + 1) = l.take k ++ [c] := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
      cases k with
      | zero =>
          simp at h
          subst c
          simp
      | succ k =>
          have hk : as[k]? = some c := by simpa using h
          simpa using congrArg (List.cons a) (ih k hk)

theorem hitSet9_single {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (c : I.ID) (y : Fin N) :
    y ∈ hitSet9 E G ω {c} ↔ Hits E G (anc9 ω c) y := by
  simp [hitSet9]

def starCoord9 {n : ℕ} (v : EvenSites9 n) (j : Fin n) : StarOdd9 v :=
  ⟨⟨cubeFlip v.1 j, fun h => ((cubeFlip_parity v.1 j).mp h) v.2⟩,
    cubeFlip_adj v.1 j⟩

noncomputable def starCoordEquiv9 {n : ℕ} (v : EvenSites9 n) :
    Fin n ≃ StarOdd9 v :=
  Equiv.ofBijective (starCoord9 v) (by
    constructor
    · intro i j hij
      by_contra hne
      have hodd : (starCoord9 v i).1 = (starCoord9 v j).1 :=
        congrArg (fun b : StarOdd9 v => b.1) hij
      have hvalue : cubeFlip v.1 i = cubeFlip v.1 j :=
        congrArg (fun b : OddSites9 n => b.1) hodd
      have hAt := congrFun hvalue i
      have hji : i ≠ j := hne
      cases hv : v.1 i <;> simp [cubeFlip, hji, hv] at hAt
    · intro b
      have hcard :
          (Finset.univ.filter (fun i : Fin n => v.1 i ≠ b.1.1 i)).card = 1 := by
        have hb := b.2
        change (Finset.univ.filter (fun i : Fin n => v.1 i ≠ b.1.1 i)).card = 1 at hb
        exact hb
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
      refine ⟨i, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      funext j
      by_cases hji : j = i
      · subst j
        have himem : i ∈ Finset.univ.filter (fun k : Fin n => v.1 k ≠ b.1.1 k) := by
          rw [hi]
          simp
        have hdiff := (Finset.mem_filter.mp himem).2
        cases hv : v.1 i <;> cases hb : b.1.1 i <;>
          simp_all [starCoord9, cubeFlip, hv, hb]
      · have hsame : v.1 j = b.1.1 j := by
          by_contra hne
          have hjmem : j ∈ Finset.univ.filter (fun k : Fin n => v.1 k ≠ b.1.1 k) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
          rw [hi] at hjmem
          exact hji (Finset.mem_singleton.mp hjmem)
        simp [starCoord9, cubeFlip, hji, hsame])

noncomputable def specialCoordEquiv9 {m n : ℕ} (hm : m ≤ n) :
    Fin m ≃ {j : Fin n // j.val < m} :=
  Equiv.ofBijective (fun i : Fin m =>
    (⟨Fin.castLE hm i, by simpa using i.isLt⟩ : {j : Fin n // j.val < m})) (by
      constructor
      · intro i j hij
        apply Fin.ext
        have hval := congrArg (fun q : {j : Fin n // j.val < m} => q.1.val) hij
        simpa using hval
      · intro j
        refine ⟨⟨j.1.val, j.2⟩, ?_⟩
        apply Subtype.ext
        apply Fin.ext
        rfl)

theorem orderRegular_degree_lower {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} {E : Fin N → Fin N → Prop} {G : Colour}
    (ω : Outcome9 I N) (base : Law N) (order : List I.ID)
    (hregular : orderRegular9 E G ω base order) (hsmall : P.bStar n ≤ 1 / 200) :
    ∀ k c, order[k]? = some c →
      (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro c hget
      have hstep := hregular k c hget (by
        intro j c' hj hjget
        exact ih j hj c' hjget)
      have habs := abs_le.mp hstep
      have hsmall' : 2 * P.bStar n ≤ (1 / 100 : ℝ) := by linarith
      linarith

theorem specialWord9_starCoord {P : Params9} {n : ℕ} (v : EvenSites9 n) (j : Fin n)
    (hm : P.m n ≤ n) (hj : j.val < P.m n) :
    specialWord9 (P.m n) (cubeFlip v.1 j) =
      flipWord9 (specialWord9 (P.m n) v.1) ⟨j.val, hj⟩ := by
  classical
  funext k
  have hk : k.val < n := lt_of_lt_of_le k.isLt hm
  by_cases hkj : k.val = j.val
  · have hidx : (⟨k.val, hk⟩ : Fin n) = j := Fin.ext hkj
    have hkm : k = (⟨j.val, hj⟩ : Fin (P.m n)) := Fin.ext hkj
    subst k
    simp [specialWord9, cubeFlip, flipWord9, hidx]
  · have hidx : (⟨k.val, hk⟩ : Fin n) ≠ j := by
      intro heq
      have hval : k.val = j.val := by simpa using congrArg Fin.val heq
      exact hkj hval
    have hkm : k ≠ (⟨j.val, hj⟩ : Fin (P.m n)) := by
      intro heq
      have hval : k.val = j.val := by simpa using congrArg Fin.val heq
      exact hkj hval
    simp [specialWord9, cubeFlip, flipWord9, hidx, hkm]

theorem specialWord9_starCoord_residual {P : Params9} {n : ℕ} (v : EvenSites9 n)
    (j : Fin n) (hm : P.m n ≤ n) (hj : P.m n ≤ j.val) :
    specialWord9 (P.m n) (cubeFlip v.1 j) = specialWord9 (P.m n) v.1 := by
  classical
  funext k
  have hk : k.val < n := lt_of_lt_of_le k.isLt hm
  have hidx : (⟨k.val, hk⟩ : Fin n) ≠ j := by
    intro heq
    have hval : k.val = j.val := by simpa using congrArg Fin.val heq
    exact (ne_of_lt (lt_of_lt_of_le k.isLt hj)) hval
  simp [specialWord9, cubeFlip, hm, hk, hidx]

private theorem hitSet9_union_single {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (ids : Finset I.ID) (c : I.ID) :
    hitSet9 E G ω (ids ∪ {c}) = hitSet9 E G ω ids ∩ hitSet9 E G ω {c} := by
  ext y
  simp [hitSet9]
  exact and_comm

theorem prefixHitSet9_succ {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (E : Fin N → Fin N → Prop) (G : Colour) (ω : Outcome9 I N)
    (order : List I.ID) (k : ℕ) (c : I.ID) (h : order[k]? = some c) :
    hitSet9 E G ω (order.take (k + 1)).toFinset =
      hitSet9 E G ω (order.take k).toFinset ∩ hitSet9 E G ω {c} := by
  rw [list_take_succ_eq_append_of_getElem? order k c h]
  have hset : (order.take k ++ [c]).toFinset = (order.take k).toFinset ∪ {c} := by simp
  rw [hset]
  exact hitSet9_union_single (M := M) E G ω (order.take k).toFinset c

theorem restrict_mass_inter {N : ℕ} (μ : Law N) (A B : Finset (Fin N))
    (hA : 0 < ∑ y ∈ A, μ.w y) :
    (∑ y ∈ B, (μ.restrict A hA).w y) =
      (∑ y ∈ A ∩ B, μ.w y) / (∑ y ∈ A, μ.w y) := by
  classical
  have hfilter : B.filter (fun y => y ∈ A) = A ∩ B := by
    ext y
    simp [and_comm]
  unfold Law.restrict
  calc
    (∑ y ∈ B, if y ∈ A then μ.w y / (∑ z ∈ A, μ.w z) else 0) =
        ∑ y ∈ B.filter (fun y => y ∈ A), μ.w y / (∑ z ∈ A, μ.w z) := by
          rw [← Finset.sum_filter]
    _ = ∑ y ∈ A ∩ B, μ.w y / (∑ z ∈ A, μ.w z) := by rw [hfilter]
    _ = (∑ y ∈ A ∩ B, μ.w y) / (∑ z ∈ A, μ.w z) := by rw [Finset.sum_div]

theorem restrictOr9_inter_assoc {N : ℕ} (μ : Law N) (A B : Finset (Fin N))
    (hA : 0 < ∑ y ∈ A, μ.w y) (hAB : 0 < ∑ y ∈ A ∩ B, μ.w y) :
    restrictOr9 (restrictOr9 μ A) B = restrictOr9 μ (A ∩ B) := by
  classical
  have hfirst : restrictOr9 μ A = μ.restrict A hA := by
    simp [restrictOr9, hA]
  have hfilter : B.filter (fun y => y ∈ A) = A ∩ B := by
    ext y
    simp [and_comm]
  have hmassEq :
      (∑ y ∈ B, (μ.restrict A hA).w y) =
        (∑ y ∈ A ∩ B, μ.w y) / (∑ y ∈ A, μ.w y) := by
    unfold Law.restrict
    calc
      (∑ y ∈ B, if y ∈ A then μ.w y / (∑ z ∈ A, μ.w z) else 0) =
          ∑ y ∈ B.filter (fun y => y ∈ A), μ.w y / (∑ z ∈ A, μ.w z) := by
            rw [← Finset.sum_filter]
      _ = ∑ y ∈ A ∩ B, μ.w y / (∑ z ∈ A, μ.w z) := by rw [hfilter]
      _ = (∑ y ∈ A ∩ B, μ.w y) / (∑ z ∈ A, μ.w z) := by rw [Finset.sum_div]
  have hmassPos : 0 < ∑ y ∈ B, (μ.restrict A hA).w y := by
    rw [hmassEq]
    exact div_pos hAB hA
  have hmassLeft : 0 < ∑ y ∈ B, (restrictOr9 μ A).w y := by
    rw [hfirst]
    exact hmassPos
  have hstep : restrictOr9 (restrictOr9 μ A) B = (μ.restrict A hA).restrict B hmassPos := by
    calc
      restrictOr9 (restrictOr9 μ A) B = restrictOr9 (μ.restrict A hA) B :=
        congrArg (fun ν => restrictOr9 ν B) hfirst
      _ = (μ.restrict A hA).restrict B hmassPos := by
        simp [restrictOr9, hmassPos]
  calc
    restrictOr9 (restrictOr9 μ A) B = (μ.restrict A hA).restrict B hmassPos := hstep
    _ = μ.restrict (A ∩ B) hAB := by
      apply finprob_ext
      intro y
      change (if y ∈ B then
          (μ.restrict A hA).w y / (∑ z ∈ B, (μ.restrict A hA).w z) else 0) =
        (if y ∈ A ∩ B then μ.w y / (∑ z ∈ A ∩ B, μ.w z) else 0)
      rw [hmassEq]
      by_cases hyA : y ∈ A
      · by_cases hyB : y ∈ B
        · simp [hyA, hyB, Finset.mem_inter, Law.restrict]
          field_simp [ne_of_gt hA, ne_of_gt hAB]
          <;> ring
        · simp [hyA, hyB, Finset.mem_inter]
      · by_cases hyB : y ∈ B
        · simp [hyA, hyB, Finset.mem_inter, Law.restrict]
        · simp [hyA, hyB, Finset.mem_inter]
    _ = restrictOr9 μ (A ∩ B) := by simp [restrictOr9, hAB]

theorem expect_hitInd_eq_rowDeg {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (x : Fin N) :
    μ.expect (hitInd9 E G x) = rowDeg E G x μ := by
  simp [FinProb.expect, rowDeg, hitInd9]

/-- Conditioning once more on a hit changes the target degree by covariance divided by the hit mass. -/
theorem rowDeg_restrictOr_cov_shift {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (A B : Finset (Fin N)) (w x : Fin N)
    (hA : 0 < ∑ y ∈ A, μ.w y) (hAB : 0 < ∑ y ∈ A ∩ B, μ.w y)
    (hB : ∀ y, y ∈ B ↔ Hits E G w y) :
    rowDeg E G x (restrictOr9 μ (A ∩ B)) - rowDeg E G x (restrictOr9 μ A) =
      (FinProb.expect (restrictOr9 μ A)
          (fun y => hitInd9 E G w y * hitInd9 E G x y) -
        rowDeg E G w (restrictOr9 μ A) * rowDeg E G x (restrictOr9 μ A)) /
        rowDeg E G w (restrictOr9 μ A) := by
  classical
  let lam := restrictOr9 μ A
  change rowDeg E G x (restrictOr9 μ (A ∩ B)) - rowDeg E G x lam =
    (FinProb.expect lam (fun y => hitInd9 E G w y * hitInd9 E G x y) -
      rowDeg E G w lam * rowDeg E G x lam) / rowDeg E G w lam
  have hfirst : restrictOr9 μ A = μ.restrict A hA := by
    simp [restrictOr9, hA]
  have hmassLam :
      (∑ y ∈ B, lam.w y) = (∑ y ∈ A ∩ B, μ.w y) / (∑ y ∈ A, μ.w y) := by
    change (∑ y ∈ B, (restrictOr9 μ A).w y) = _
    rw [hfirst]
    exact restrict_mass_inter μ A B hA
  have hmassLamPos : 0 < ∑ y ∈ B, lam.w y := by
    rw [hmassLam]
    exact div_pos hAB hA
  have hden : (∑ y ∈ B, lam.w y) = rowDeg E G w lam :=
    restrictOr_hit_mass_eq_rowDeg E G lam B w hB
  have hdenPos : 0 < rowDeg E G w lam := by rw [← hden]; exact hmassLamPos
  have hcompose : restrictOr9 lam B = restrictOr9 μ (A ∩ B) := by
    exact restrictOr9_inter_assoc μ A B hA hAB
  have hnext : rowDeg E G x (restrictOr9 lam B) =
      (∑ y, lam.w y * (hitInd9 E G w y * hitInd9 E G x y)) /
        rowDeg E G w lam := by
    rw [rowDeg_restrictOr_hit_formula E G lam B w x hB hmassLamPos, hden]
  have hprod : FinProb.expect lam (fun y => hitInd9 E G w y * hitInd9 E G x y) =
      ∑ y, lam.w y * (hitInd9 E G w y * hitInd9 E G x y) := rfl
  rw [← hcompose, hnext]
  rw [hprod]
  field_simp [ne_of_gt hdenPos]
  <;> ring

theorem abs_sub_seq_le {f : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) :
    ∀ m, (∀ k < m, |f (k + 1) - f k| ≤ K) → |f m - f 0| ≤ m * K := by
  intro m
  induction m with
  | zero =>
      intro h
      simp
  | succ m ih =>
      intro h
      have hstep : |f (m + 1) - f m| ≤ K := h m (by omega)
      have hprev : |f m - f 0| ≤ m * K := ih (by
        intro k hk
        exact h k (by omega))
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_cast
      rw [hcast]
      calc
        |f (m + 1) - f 0| = |(f (m + 1) - f m) + (f m - f 0)| := by congr 1 <;> ring
        _ ≤ |f (m + 1) - f m| + |f m - f 0| := abs_add_le _ _
        _ ≤ K + m * K := add_le_add hstep hprev
        _ = ((m : ℝ) + 1) * K := by ring

theorem eventual_const_mul_rpow_neg_lt {d A ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, A * (n : ℝ) ^ (-d) < ε := by
  have hlim : Tendsto (fun n : ℕ => A * (n : ℝ) ^ (-d)) atTop (𝓝 0) := by
    simpa [mul_assoc] using Tendsto.const_mul A
      ((tendsto_rpow_neg_atTop hd).comp tendsto_natCast_atTop_atTop)
  have hsmall : ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ (-d) < ε :=
    hlim.eventually (Iio_mem_nhds hε)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hsmall
  exact ⟨n₀, fun n hn => hn₀ n hn⟩

theorem core_order_hit_shift_bound {P : Params9} {n N : ℕ} {M : TagMix N}
    (S : Setup9 P n N M) (I : IDMap9 P n) (E : Fin N → Fin N → Prop) (G : Colour)
    (ω : Outcome9 I N) (v : EvenSites9 n) (b : OddSites9 n)
    (hregular : orderRegular9 E G ω (siteSecond9 S b.1) (coreOrder9 I v b))
    (hsmall : P.bStar n ≤ 1 / 200)
    (hCov : ∀ k, k < (coreOrder9 I v b).length →
      |coreCov9 S E G ω v b k| ≤
        P.aStar n * (n : ℝ) ^ (-(2 * (P.χ : ℝ))))
    (hn : 1 ≤ n)
    (hlen : ((coreOrder9 I v b).length : ℝ) ≤ (n : ℝ) ^ (P.χ : ℝ)) :
    |rowDeg E G (anc9 ω (I.center v.1))
        (restrictOr9 (siteSecond9 S b.1) (coreHitSet9 E G ω v b)) -
      rowDeg E G (anc9 ω (I.center v.1)) (siteSecond9 S b.1)| ≤
      3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) := by
  classical
  let order := coreOrder9 I v b
  let base := siteSecond9 S b.1
  let x := anc9 ω (I.center v.1)
  let massPrefix := fun k =>
    ∑ y ∈ hitSet9 E G ω (order.take k).toFinset, base.w y
  let degreePrefix := fun k => rowDeg E G x (prefixLaw9 E G ω base order k)
  let len := order.length
  let stepSize := P.aStar n * (n : ℝ) ^ (-(2 * (P.χ : ℝ)))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have haStarPos : 0 < P.aStar n := by
    dsimp [Params9.aStar]
    exact div_pos (Real.rpow_pos_of_pos hnR _) (by norm_num)
  have hstepSizeNonneg : 0 ≤ stepSize := by
    dsimp [stepSize]
    exact mul_nonneg haStarPos.le (Real.rpow_nonneg (le_of_lt hnR) _)
  have hthreeStepNonneg : 0 ≤ 3 * stepSize :=
    mul_nonneg (by norm_num) hstepSizeNonneg
  have hmass0 : massPrefix 0 = 1 := by
    simp [massPrefix, order, base, hitSet9, (siteSecond9 S b.1).sum_eq_one]
  have hGood : ∀ k, k ≤ len →
      0 < massPrefix k ∧
      ∀ j, j < k → ∀ c, order[j]? = some c →
        (49 / 100 : ℝ) ≤
          rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order j) := by
    intro k
    induction k with
    | zero =>
        intro hk
        constructor
        · rw [hmass0]
          norm_num
        · intro j hj
          omega
    | succ k ih =>
        intro hk
        have hklt : k < len := by omega
        have hprev := ih (by omega)
        let c := order[k]'hklt
        have hget : order[k]? = some c := by simp [c]
        have hregK :
            |rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order k) - 1 / 2| ≤
              2 * P.bStar n := by
          apply hregular k c hget
          intro j c' hj hjget
          exact hprev.2 j hj c' hjget
        have hdegK : (49 / 100 : ℝ) ≤
            rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order k) := by
          have habs := abs_le.mp hregK
          have hsmall' : 2 * P.bStar n ≤ (1 / 100 : ℝ) := by linarith
          linarith
        let A := hitSet9 E G ω (order.take k).toFinset
        let B := hitSet9 E G ω {c}
        have hApos : 0 < ∑ y ∈ A, base.w y := by
          simpa [massPrefix, A, order, base] using hprev.1
        have hB : ∀ y, y ∈ B ↔ Hits E G (anc9 ω c) y := by
          dsimp [B]
          intro y
          exact hitSet9_single (M := M) E G ω c y
        have hmassB_eq :
            (∑ y ∈ B, (restrictOr9 base A).w y) =
              rowDeg E G (anc9 ω c) (restrictOr9 base A) :=
          restrictOr_hit_mass_eq_rowDeg E G (restrictOr9 base A) B (anc9 ω c) hB
        have hmassB : 0 < ∑ y ∈ B, (restrictOr9 base A).w y := by
          rw [hmassB_eq]
          have hdegPos : 0 < rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order k) :=
            lt_of_lt_of_le (by norm_num) hdegK
          simpa [prefixLaw9, A, order, base] using hdegPos
        have hfirst : restrictOr9 base A = base.restrict A hApos := by
          simp [restrictOr9, hApos]
        have hmassRatio := restrict_mass_inter base A B hApos
        rw [← hfirst] at hmassRatio
        have hmassInter : 0 < ∑ y ∈ A ∩ B, base.w y := by
          by_contra hnot
          have hnonpos : (∑ y ∈ A ∩ B, base.w y) ≤ 0 := le_of_not_gt hnot
          have hratioNonpos :
              (∑ y ∈ A ∩ B, base.w y) / (∑ y ∈ A, base.w y) ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg hnonpos hApos.le
          rw [hmassRatio] at hmassB
          linarith
        have hprefix :
            hitSet9 E G ω (order.take (k + 1)).toFinset = A ∩ B := by
          simpa [A, B] using
            prefixHitSet9_succ (M := M) E G ω order k c hget
        have hmassNew : 0 < massPrefix (k + 1) := by
          change 0 < ∑ y ∈ hitSet9 E G ω (order.take (k + 1)).toFinset, base.w y
          rw [hprefix]
          exact hmassInter
        refine ⟨hmassNew, ?_⟩
        intro j hj c' hjget
        by_cases hjk : j = k
        · subst j
          have hopt : some c' = some c := hjget.symm.trans hget
          have hval : c' = c := Option.some.inj hopt
          subst c'
          exact hdegK
        · exact hprev.2 j (by omega) c' hjget
  have hstep : ∀ k, k < len →
      |degreePrefix (k + 1) - degreePrefix k| ≤ 3 * stepSize := by
    intro k hk
    have hklt : k < order.length := by simpa [order, len] using hk
    let c := order[k]'hklt
    have hget : order[k]? = some c := by simp [c]
    let A := hitSet9 E G ω (order.take k).toFinset
    let B := hitSet9 E G ω {c}
    have hApos : 0 < ∑ y ∈ A, base.w y := by
      simpa [massPrefix, A, order, base] using (hGood k (by omega)).1
    have hprefix :
        hitSet9 E G ω (order.take (k + 1)).toFinset = A ∩ B := by
      simpa [A, B] using prefixHitSet9_succ (M := M) E G ω order k c hget
    have hmassNext : 0 < massPrefix (k + 1) := (hGood (k + 1) (by omega)).1
    have hAB : 0 < ∑ y ∈ A ∩ B, base.w y := by
      change 0 < ∑ y ∈ hitSet9 E G ω (order.take (k + 1)).toFinset, base.w y at hmassNext
      rw [hprefix] at hmassNext
      exact hmassNext
    have hB : ∀ y, y ∈ B ↔ Hits E G (anc9 ω c) y := by
      dsimp [B]
      intro y
      exact hitSet9_single (M := M) E G ω c y
    have hshift := rowDeg_restrictOr_cov_shift E G base A B (anc9 ω c) x hApos hAB hB
    have hprefix0 : prefixLaw9 E G ω base order k = restrictOr9 base A := rfl
    have hprefix1 : prefixLaw9 E G ω base order (k + 1) = restrictOr9 base (A ∩ B) := by
      change restrictOr9 base (hitSet9 E G ω (order.take (k + 1)).toFinset) = _
      rw [hprefix]
    rw [← hprefix1, ← hprefix0] at hshift
    have hcoreCov : coreCov9 S E G ω v b k =
        FinProb.expect (prefixLaw9 E G ω base order k)
            (fun y => hitInd9 E G (anc9 ω c) y * hitInd9 E G x y) -
          rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order k) *
            rowDeg E G x (prefixLaw9 E G ω base order k) := by
      simp [coreCov9, order, hget, expect_hitInd_eq_rowDeg, base, x]
    rw [← hcoreCov] at hshift
    have hdelta : degreePrefix (k + 1) - degreePrefix k =
        coreCov9 S E G ω v b k /
          rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order k) := by
      simpa [degreePrefix] using hshift
    have hdenLow : (49 / 100 : ℝ) ≤
        rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order k) :=
      (hGood (k + 1) (by omega)).2 k (by omega) c hget
    have hdenPos : 0 < rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order k) :=
      lt_of_lt_of_le (by norm_num) hdenLow
    have hcovBound : |coreCov9 S E G ω v b k| ≤ stepSize := by
      dsimp [stepSize]
      exact hCov k hklt
    have hstepRatio : |coreCov9 S E G ω v b k /
        rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order k)| ≤ 3 * stepSize := by
      rw [abs_div, abs_of_pos hdenPos]
      calc
        |coreCov9 S E G ω v b k| /
            rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order k) ≤
          stepSize /
            rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order k) :=
              div_le_div_of_nonneg_right hcovBound hdenPos.le
        _ ≤ 3 * stepSize := by
          apply (div_le_iff₀ hdenPos).2
          have hmul := mul_le_mul_of_nonneg_left hdenLow
            hthreeStepNonneg
          nlinarith
    calc
      |degreePrefix (k + 1) - degreePrefix k| =
          |coreCov9 S E G ω v b k /
            rowDeg E G (anc9 ω c) (prefixLaw9 E G ω base order k)| := by rw [hdelta]
      _ ≤ 3 * stepSize := hstepRatio
  have htotal := abs_sub_seq_le (f := degreePrefix) (K := 3 * stepSize)
    hthreeStepNonneg len hstep
  have hpow : (n : ℝ) ^ (P.χ : ℝ) * (n : ℝ) ^ (-(2 * (P.χ : ℝ))) =
      (n : ℝ) ^ (-(P.χ : ℝ)) := by
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  have hlengthMul : (len : ℝ) * (3 * stepSize) ≤
      (n : ℝ) ^ (P.χ : ℝ) * (3 * stepSize) :=
    mul_le_mul_of_nonneg_right hlen hthreeStepNonneg
  have hlast : degreePrefix len =
      rowDeg E G x (restrictOr9 base (coreHitSet9 E G ω v b)) := by
    have horderSet : (order.take len).toFinset = coreIDs9 I v b := by
      dsimp [order, len, coreOrder9]
      rw [List.take_length]
      simp [coreIDs9]
    change rowDeg E G x (restrictOr9 base
        (hitSet9 E G ω (order.take len).toFinset)) = _
    rw [horderSet]
    rfl
  have hzero : degreePrefix 0 = rowDeg E G x base := by
    have hrestrict : restrictOr9 base Finset.univ = base := by
      apply finprob_ext
      intro y
      simp [restrictOr9, Law.restrict, base.sum_eq_one]
    simp [degreePrefix, prefixLaw9, order, hitSet9, hrestrict]
  rw [hlast, hzero] at htotal
  calc
    |rowDeg E G x (restrictOr9 base (coreHitSet9 E G ω v b)) - rowDeg E G x base| ≤
        (len : ℝ) * (3 * stepSize) := htotal
    _ ≤ (n : ℝ) ^ (P.χ : ℝ) * (3 * stepSize) := hlengthMul
    _ = 3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) := by
      dsimp [stepSize]
      rw [← hpow]
      ring

theorem pr_exists_finset_le_sum {Ω α : Type*} [Fintype Ω] (Q : FinProb Ω)
    (s : Finset α) (A : α → Ω → Prop) :
    Q.pr (fun ω => ∃ a ∈ s, A a ω) ≤ ∑ a ∈ s, Q.pr (A a) := by
  classical
  let bad : Ω → Prop := fun ω => ∃ a ∈ s, A a ω
  change Q.pr bad ≤ ∑ a ∈ s, Q.pr (A a)
  unfold FinProb.pr
  calc
    (∑ ω, @ite ℝ (bad ω) (Classical.propDecidable _) (Q.w ω) 0) ≤
        ∑ ω, ∑ a ∈ s, if A a ω then Q.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hex : bad ω
      · obtain ⟨a, ha, hAω⟩ := hex
        have hbad : bad ω := ⟨a, ha, hAω⟩
        have hsingle : Q.w ω ≤ ∑ a ∈ s, if A a ω then Q.w ω else 0 := by
          have := Finset.single_le_sum
            (f := fun a => if A a ω then Q.w ω else 0)
            (fun b hb => by split_ifs <;> simp [Q.nonneg]) ha
          simpa [hAω] using this
        simpa [hbad] using hsingle
      · have hnonneg : 0 ≤ ∑ a ∈ s, if A a ω then Q.w ω else 0 := by
          apply Finset.sum_nonneg
          intro a ha
          split_ifs <;> simp [Q.nonneg]
        have hbad : ¬ bad ω := hex
        simpa [hbad] using hnonneg
    _ = ∑ a ∈ s, Q.pr (A a) := by
      rw [Finset.sum_comm]
      simp [FinProb.pr]

theorem eventual_poly_tail {u c A s : ℝ} (hu : 0 < u) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      A * (n : ℝ) ^ s * Real.exp (-c * (n : ℝ) ^ u) ≤
        Real.exp (-((c / 2) * (n : ℝ) ^ u)) := by
  have hlim := tendsto_nat_rpow_exp_neg_rpow (s := s) (u := u) (c := c / 2)
    hu (by linarith)
  have hseq : Tendsto (fun n : ℕ => A * (n : ℝ) ^ s *
      Real.exp (-((c / 2) * (n : ℝ) ^ u))) atTop (𝓝 0) := by
    simpa [mul_assoc] using Tendsto.const_mul A hlim
  have hsmall : ∀ᶠ n : ℕ in atTop,
      A * (n : ℝ) ^ s * Real.exp (-((c / 2) * (n : ℝ) ^ u)) < 1 :=
    hseq.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hsmall
  refine ⟨n₀, ?_⟩
  intro n hn
  let e : ℝ := Real.exp (-((c / 2) * (n : ℝ) ^ u))
  have he : 0 < e := by dsimp [e]; exact Real.exp_pos _
  have hq : A * (n : ℝ) ^ s * e < 1 := by simpa [e] using hn₀ n hn
  have hsplit : Real.exp (-c * (n : ℝ) ^ u) = e * e := by
    dsimp [e]
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    A * (n : ℝ) ^ s * Real.exp (-c * (n : ℝ) ^ u) =
        (A * (n : ℝ) ^ s * e) * e := by rw [hsplit]; ring
    _ ≤ 1 * e := mul_le_mul_of_nonneg_right hq.le he.le
    _ = e := by ring
    _ = Real.exp (-((c / 2) * (n : ℝ) ^ u)) := by rfl

theorem eventual_tail_sum2 {u c₁ c₂ : ℝ} (hu : 0 < u) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Real.exp (-c₁ * (n : ℝ) ^ u) + Real.exp (-c₂ * (n : ℝ) ^ u) ≤
        Real.exp (-((min c₁ c₂ / 2) * (n : ℝ) ^ u)) := by
  let C : ℝ := min c₁ c₂
  have hC : 0 < C := by dsimp [C]; exact lt_min hc₁ hc₂
  have hC₁ : C ≤ c₁ := by dsimp [C]; exact min_le_left _ _
  have hC₂ : C ≤ c₂ := by dsimp [C]; exact min_le_right _ _
  have hu0 : Tendsto (fun n : ℕ => Real.exp (-(C / 2) * (n : ℝ) ^ u)) atTop (𝓝 0) := by
    simpa using (tendsto_nat_rpow_exp_neg_rpow (s := 0) (u := u) (c := C / 2)
      hu (by linarith))
  have hsmall : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(C / 2) * (n : ℝ) ^ u) < 1 / 2 :=
    hu0.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hsmall
  refine ⟨n₀, ?_⟩
  intro n hn
  have hx : 0 ≤ (n : ℝ) ^ u := Real.rpow_nonneg (by positivity) _
  have h₁ : Real.exp (-c₁ * (n : ℝ) ^ u) ≤ Real.exp (-C * (n : ℝ) ^ u) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hC₁) hx]
  have h₂ : Real.exp (-c₂ * (n : ℝ) ^ u) ≤ Real.exp (-C * (n : ℝ) ^ u) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hC₂) hx]
  let q : ℝ := Real.exp (-(C / 2) * (n : ℝ) ^ u)
  have hq : q < 1 / 2 := hn₀ n hn
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hexp : Real.exp (-C * (n : ℝ) ^ u) = q * q := by
    dsimp [q]
    rw [← Real.exp_add]
    congr 1
    ring
  have hmul : 2 * q * q ≤ q := by nlinarith [mul_le_mul_of_nonneg_right hq.le hq0]
  calc
    Real.exp (-c₁ * (n : ℝ) ^ u) + Real.exp (-c₂ * (n : ℝ) ^ u) ≤
        2 * Real.exp (-C * (n : ℝ) ^ u) := by linarith
    _ = 2 * q * q := by rw [hexp]; ring
    _ ≤ q := hmul
    _ = Real.exp (-((min c₁ c₂ / 2) * (n : ℝ) ^ u)) := by
      dsimp [q, C]
      congr 1
      ring

theorem eventual_mean_error_bound (P : Params9) (hP : P.Valid)
    (C₁ C₂ c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 +
        P.tail c₁ n + P.tail c₂ n + 3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) ≤
          P.aStar n / 100 := by
  rcases hP with ⟨⟨hxS, _, _⟩, ⟨hminus, hminusPlus, hplus⟩, _, _,
    ⟨hchi, hchiBound⟩, hgap, _⟩
  have hu : 0 < P.u := by
    dsimp [Params9.u]
    positivity
  have hmin : min P.xS (min P.hMinus (1 - P.hPlus)) ≤ P.hMinus :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hchiBoundR : (P.χ : ℝ) <
      ((min P.xS (min P.hMinus (1 - P.hPlus)) : ℚ) : ℝ) / 100 := by
    exact_mod_cast hchiBound
  have hminR : ((min P.xS (min P.hMinus (1 - P.hPlus)) : ℚ) : ℝ) ≤
      (P.hMinus : ℝ) := by exact_mod_cast hmin
  have hchiMinus : (P.χ : ℝ) < (P.hMinus : ℝ) / 100 := by linarith
  have hmargin : (P.χ : ℝ) + (P.hPlus : ℝ) - 2 * (P.hMinus : ℝ) < 0 := by
    have hg : (P.hPlus : ℝ) - (P.hMinus : ℝ) < (P.χ : ℝ) / 10 := by
      exact_mod_cast hgap
    have hχm : 0 < (P.hMinus : ℝ) := by exact_mod_cast hminus
    have hχbound' : (P.χ : ℝ) < (P.hMinus : ℝ) / 100 := hchiMinus
    linarith
  have hchiR : 0 < (P.χ : ℝ) := by exact_mod_cast hchi
  let α : ℝ := (P.χ : ℝ) + (P.hPlus : ℝ) - 2 * (P.hMinus : ℝ)
  have hα : α < 0 := by dsimp [α]; exact hmargin
  have hpseq : Tendsto (fun n : ℕ => 2 * (C₁ + C₂) * (n : ℝ) ^ α) atTop (𝓝 0) := by
    simpa [mul_assoc, neg_neg] using
      (Tendsto.const_mul (2 * (C₁ + C₂))
        ((tendsto_rpow_neg_atTop (neg_pos.mpr hα)).comp tendsto_natCast_atTop_atTop))
  have ht₁ : Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ (P.hPlus : ℝ) *
      Real.exp (-c₁ * (n : ℝ) ^ P.u)) atTop (𝓝 0) := by
    simpa [mul_assoc] using
      (Tendsto.const_mul 2
        (tendsto_nat_rpow_exp_neg_rpow (s := P.hPlus) (u := P.u) (c := c₁) hu hc₁))
  have ht₂ : Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ (P.hPlus : ℝ) *
      Real.exp (-c₂ * (n : ℝ) ^ P.u)) atTop (𝓝 0) := by
    simpa [mul_assoc] using
      (Tendsto.const_mul 2
        (tendsto_nat_rpow_exp_neg_rpow (s := P.hPlus) (u := P.u) (c := c₂) hu hc₂))
  have hχseq : Tendsto (fun n : ℕ => 3 * (n : ℝ) ^ (-(P.χ : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def, mul_assoc] using
      (Tendsto.const_mul 3
        ((tendsto_rpow_neg_atTop hchiR).comp tendsto_natCast_atTop_atTop))
  have hsmall₁ : ∀ᶠ n : ℕ in atTop, 2 * (C₁ + C₂) * (n : ℝ) ^ α < 1 / 400 :=
    hpseq.eventually (Iio_mem_nhds (by norm_num))
  have hsmall₂ : ∀ᶠ n : ℕ in atTop,
      2 * (n : ℝ) ^ (P.hPlus : ℝ) * Real.exp (-c₁ * (n : ℝ) ^ P.u) < 1 / 400 :=
    ht₁.eventually (Iio_mem_nhds (by norm_num))
  have hsmall₃ : ∀ᶠ n : ℕ in atTop,
      2 * (n : ℝ) ^ (P.hPlus : ℝ) * Real.exp (-c₂ * (n : ℝ) ^ P.u) < 1 / 400 :=
    ht₂.eventually (Iio_mem_nhds (by norm_num))
  have hsmall₄ : ∀ᶠ n : ℕ in atTop, 3 * (n : ℝ) ^ (-(P.χ : ℝ)) < 1 / 400 :=
    hχseq.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 hsmall₁
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.1 hsmall₂
  obtain ⟨n₃, hn₃⟩ := eventually_atTop.1 hsmall₃
  obtain ⟨n₄, hn₄⟩ := eventually_atTop.1 hsmall₄
  refine ⟨max (max (max n₁ n₂) (max n₃ n₄)) 1, ?_⟩
  intro n hn
  have hn₁' : n₁ ≤ n := by omega
  have hn₂' : n₂ ≤ n := by omega
  have hn₃' : n₃ ≤ n := by omega
  have hn₄' : n₄ ≤ n := by omega
  have hn0 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have ha : 0 < P.aStar n := by
    dsimp [Params9.aStar]
    positivity
  have hratio₁ :
      (C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 / P.aStar n =
        2 * (C₁ + C₂) * (n : ℝ) ^ α := by
    dsimp [α, Params9.aStar, Params9.bStar]
    calc
      (C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * ((n : ℝ) ^ (-(P.hMinus : ℝ))) ^ 2 /
          ((n : ℝ) ^ (-(P.hPlus : ℝ)) / 2) =
          (C₁ + C₂) * ((n : ℝ) ^ (P.χ : ℝ) *
            ((n : ℝ) ^ (-(P.hMinus : ℝ))) ^ 2 /
              ((n : ℝ) ^ (-(P.hPlus : ℝ)) / 2)) := by ring
      _ = (C₁ + C₂) * (2 * (n : ℝ) ^
            ((P.χ : ℝ) + (P.hPlus : ℝ) - 2 * (P.hMinus : ℝ))) := by
          rw [power_ratio n hn0 (P.χ : ℝ) (P.hMinus : ℝ) (P.hPlus : ℝ)]
      _ = 2 * (C₁ + C₂) * (n : ℝ) ^ α := by
          dsimp [α]
          ring
  have hratio₂ : P.tail c₁ n / P.aStar n =
      2 * (n : ℝ) ^ (P.hPlus : ℝ) * Real.exp (-c₁ * (n : ℝ) ^ P.u) := by
    dsimp [Params9.tail, Params9.aStar]
    rw [Real.rpow_neg hnR.le]
    have hp : (n : ℝ) ^ (P.hPlus : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos hnR _).ne'
    field_simp [hp]
    <;> ring
  have hratio₃ : P.tail c₂ n / P.aStar n =
      2 * (n : ℝ) ^ (P.hPlus : ℝ) * Real.exp (-c₂ * (n : ℝ) ^ P.u) := by
    dsimp [Params9.tail, Params9.aStar]
    rw [Real.rpow_neg hnR.le]
    have hp : (n : ℝ) ^ (P.hPlus : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos hnR _).ne'
    field_simp [hp]
    <;> ring
  have hratio₄ :
      3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) / P.aStar n =
        3 * (n : ℝ) ^ (-(P.χ : ℝ)) := by
    field_simp [ha.ne']
  have h₁ :
      (C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 / P.aStar n ≤ 1 / 400 := by
    rw [hratio₁]
    exact (hn₁ n hn₁').le
  have h₂ : P.tail c₁ n / P.aStar n ≤ 1 / 400 := by
    rw [hratio₂]
    exact (hn₂ n hn₂').le
  have h₃ : P.tail c₂ n / P.aStar n ≤ 1 / 400 := by
    rw [hratio₃]
    exact (hn₃ n hn₃').le
  have h₄ :
      3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) / P.aStar n ≤ 1 / 400 := by
    rw [hratio₄]
    exact (hn₄ n hn₄').le
  have hsum :
      (C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 +
        P.tail c₁ n + P.tail c₂ n + 3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) =
        P.aStar n * ((C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 / P.aStar n +
          P.tail c₁ n / P.aStar n + P.tail c₂ n / P.aStar n +
          3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) / P.aStar n) := by
    field_simp [ha.ne']
    <;> ring
  rw [hsum]
  have hratio :
      (C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 / P.aStar n +
          P.tail c₁ n / P.aStar n + P.tail c₂ n / P.aStar n +
          3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) / P.aStar n ≤ 1 / 100 := by
    linarith
  calc
    P.aStar n * ((C₁ + C₂) * (n : ℝ) ^ (P.χ : ℝ) * P.bStar n ^ 2 / P.aStar n +
        P.tail c₁ n / P.aStar n + P.tail c₂ n / P.aStar n +
        3 * P.aStar n * (n : ℝ) ^ (-(P.χ : ℝ)) / P.aStar n) ≤
      P.aStar n * (1 / 100) := mul_le_mul_of_nonneg_left hratio ha.le
    _ = P.aStar n / 100 := by ring

theorem eventual_tail_sum3 {u c₁ c₂ c₃ : ℝ} (hu : 0 < u)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Real.exp (-c₁ * (n : ℝ) ^ u) + Real.exp (-c₂ * (n : ℝ) ^ u) +
          Real.exp (-c₃ * (n : ℝ) ^ u) ≤
        Real.exp (-((min c₁ (min c₂ c₃) / 2) * (n : ℝ) ^ u)) := by
  let C : ℝ := min c₁ (min c₂ c₃)
  have hC : 0 < C := by dsimp [C]; exact lt_min hc₁ (lt_min hc₂ hc₃)
  have hC₁ : C ≤ c₁ := by dsimp [C]; exact min_le_left _ _
  have hC₂ : C ≤ c₂ := by dsimp [C]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hC₃ : C ≤ c₃ := by dsimp [C]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hu0 : Tendsto (fun n : ℕ => Real.exp (-(C / 2) * (n : ℝ) ^ u)) atTop (𝓝 0) := by
    simpa using (tendsto_nat_rpow_exp_neg_rpow (s := 0) (u := u) (c := C / 2) hu (by linarith))
  have hsmall : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(C / 2) * (n : ℝ) ^ u) < 1 / 3 :=
    hu0.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hsmall
  refine ⟨n₀, ?_⟩
  intro n hn
  have hx : 0 ≤ (n : ℝ) ^ u := Real.rpow_nonneg (by positivity) _
  have h₁ : Real.exp (-c₁ * (n : ℝ) ^ u) ≤ Real.exp (-C * (n : ℝ) ^ u) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hC₁) hx]
  have h₂ : Real.exp (-c₂ * (n : ℝ) ^ u) ≤ Real.exp (-C * (n : ℝ) ^ u) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hC₂) hx]
  have h₃ : Real.exp (-c₃ * (n : ℝ) ^ u) ≤ Real.exp (-C * (n : ℝ) ^ u) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hC₃) hx]
  let q : ℝ := Real.exp (-(C / 2) * (n : ℝ) ^ u)
  have hq : q < 1 / 3 := hn₀ n hn
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hexp : Real.exp (-C * (n : ℝ) ^ u) = q * q := by
    dsimp [q]
    rw [← Real.exp_add]
    congr 1
    ring
  have hmul : 3 * q * q ≤ q := by nlinarith [mul_le_mul_of_nonneg_right hq.le hq0]
  calc
    Real.exp (-c₁ * (n : ℝ) ^ u) + Real.exp (-c₂ * (n : ℝ) ^ u) +
        Real.exp (-c₃ * (n : ℝ) ^ u) ≤ 3 * Real.exp (-C * (n : ℝ) ^ u) := by
          linarith
    _ = 3 * q * q := by rw [hexp]; ring
    _ ≤ q := hmul
    _ = Real.exp (-((C / 2) * (n : ℝ) ^ u)) := by
      dsimp [q]
      congr 1
      ring

noncomputable def gainMeanSpecialLoss9 (P : Params9) (n : ℕ) : ℝ :=
  match P.case with
  | .sub _ _ _ => -(P.m n : ℝ) * (2 * P.bStar n)
  | .lin _ _ _ _ => -((1 / 20 : ℝ) * P.aStar n * n)

theorem clippedFrac9_bounds {P : Params9} {n N : ℕ} {M : TagMix N}
    {S : Setup9 P n N M} {I : IDMap9 P n} {E : Fin N → Fin N → Prop} {G : Colour}
    (ω : Outcome9 I N) (v : EvenSites9 n) (b : OddSites9 n)
    (hB : 0 ≤ P.bStar n) :
    1 / 2 - 2 * P.bStar n ≤ clippedFrac9 S E G ω v b ∧
      clippedFrac9 S E G ω v b ≤ 1 / 2 + 2 * P.bStar n := by
  have hinterval : 1 / 2 - 2 * P.bStar n ≤ 1 / 2 + 2 * P.bStar n := by linarith
  constructor
  · dsimp [clippedFrac9]
    exact le_max_left _ _
  · dsimp [clippedFrac9]
    exact max_le hinterval (min_le_left _ _)

theorem eventual_gain_mean_margin9 (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ((n : ℝ) - (P.m n : ℝ)) * P.aStar n + gainMeanSpecialLoss9 P n -
          (n : ℝ) * P.aStar n / 100 ≥
        (9 / 10 : ℝ) * n * P.aStar n := by
  cases hcase : P.case with
  | lin αS αD hB yB =>
      have hbranch : 0 < 100 * αS ∧ 100 * αS < αD ∧ αD < 1 / 100 ∧
          P.σ < P.χ / 10 ∧ P.hPlus < hB ∧ hB < 1 ∧ 0 < yB ∧ yB < 1 := by
        simpa [hcase] using hP.2.2.2.2.2.2
      rcases hbranch with ⟨hαS, h100, hαD, _, _, _, _, _⟩
      have hαD100 : 100 * αD < 1 := by nlinarith [hαD]
      have hαD100R : (100 : ℝ) * (αD : ℝ) < 1 := by exact_mod_cast hαD100
      have hαDpos : 0 < αD := by linarith
      have hαDpos' : (0 : ℝ) < (αD : ℝ) := by exact_mod_cast hαDpos
      refine ⟨1, ?_⟩
      intro n hn
      have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hfloor : (P.m n : ℝ) ≤ (αD : ℝ) * n / 10 := by
        simp only [Params9.m, hcase]
        exact Nat.floor_le (by positivity)
      have hmSmall : (P.m n : ℝ) ≤ (n : ℝ) / 1000 := by
        nlinarith [hfloor, mul_lt_mul_of_pos_right hαD100R hnR]
      have ha : 0 ≤ P.aStar n := by
        dsimp [Params9.aStar]
        positivity
      have hma : (P.m n : ℝ) * P.aStar n ≤
          (n : ℝ) * P.aStar n / 1000 := by
        calc
          (P.m n : ℝ) * P.aStar n ≤ ((n : ℝ) / 1000) * P.aStar n :=
            mul_le_mul_of_nonneg_right hmSmall ha
          _ = (n : ℝ) * P.aStar n / 1000 := by ring
      simp only [gainMeanSpecialLoss9, hcase]
      nlinarith [hma]
  | sub yS yD yM =>
      have hbranch : 0 < yS ∧ yS < yM ∧ yM < 1 - P.σ ∧
          1 - P.σ < yD ∧ yD < 1 ∧ P.χ < P.σ / 10 := by
        simpa [hcase] using hP.2.2.2.2.2.2
      rcases hbranch with ⟨_, _, hym, _, _, hχσ⟩
      have hym' : (yM : ℝ) < 1 - (P.σ : ℝ) := by exact_mod_cast hym
      have hχσ' : (P.χ : ℝ) < (P.σ : ℝ) / 10 := by exact_mod_cast hχσ
      have hσ : 0 < (P.σ : ℝ) := by exact_mod_cast hP.2.2.2.1.1
      have hdiff : (P.hPlus : ℝ) - (P.hMinus : ℝ) < (P.χ : ℝ) / 10 := by
        exact_mod_cast hP.2.2.2.2.2.1
      let d₁ : ℝ := 1 - (yM : ℝ)
      let d₂ : ℝ := 1 - (yM : ℝ) - ((P.hPlus : ℝ) - (P.hMinus : ℝ))
      have hd₁ : 0 < d₁ := by dsimp [d₁]; linarith
      have hd₂ : 0 < d₂ := by dsimp [d₂]; nlinarith
      obtain ⟨n₁, hsmall₁⟩ :=
        eventual_const_mul_rpow_neg_lt (d := d₁) (A := 1) (ε := 1 / 100)
          hd₁ (by norm_num)
      obtain ⟨n₂, hsmall₂⟩ :=
        eventual_const_mul_rpow_neg_lt (d := d₂) (A := 400) (ε := 1)
          hd₂ (by norm_num)
      refine ⟨max (max n₁ n₂) 1, ?_⟩
      intro n hn
      have hn12 : max n₁ n₂ ≤ n := le_trans (le_max_left (max n₁ n₂) 1) hn
      have hn₁ : n₁ ≤ n := le_trans (le_max_left n₁ n₂) hn12
      have hn₂ : n₂ ≤ n := le_trans (le_max_right n₁ n₂) hn12
      have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hpow₁ : (n : ℝ) ^ (-(d₁)) < 1 / 100 := by
        simpa [d₁] using hsmall₁ n hn₁
      have hpow₂ : 400 * (n : ℝ) ^ (-(d₂)) < 1 := by
        simpa [d₂] using hsmall₂ n hn₂
      have hmFloor : (P.m n : ℝ) ≤ (n : ℝ) ^ (yM : ℝ) := by
        simp only [Params9.m, hcase]
        exact Nat.floor_le (by positivity)
      have hpowFactor₁ : (n : ℝ) ^ (yM : ℝ) =
          (n : ℝ) * (n : ℝ) ^ (-(d₁)) := by
        rw [show (yM : ℝ) = 1 + (-(d₁)) by dsimp [d₁]; ring,
          Real.rpow_add hnR]
        simp
      have hmSmall : (P.m n : ℝ) ≤ (n : ℝ) / 100 := by
        calc
          (P.m n : ℝ) ≤ (n : ℝ) ^ (yM : ℝ) := hmFloor
          _ = (n : ℝ) * (n : ℝ) ^ (-(d₁)) := hpowFactor₁
          _ ≤ (n : ℝ) / 100 := by nlinarith [hpow₁, hnR]
      have ha : 0 ≤ P.aStar n := by
        dsimp [Params9.aStar]
        positivity
      have hma : (P.m n : ℝ) * P.aStar n ≤
          (n : ℝ) * P.aStar n / 100 := by
        calc
          (P.m n : ℝ) * P.aStar n ≤ ((n : ℝ) / 100) * P.aStar n :=
            mul_le_mul_of_nonneg_right hmSmall ha
          _ = (n : ℝ) * P.aStar n / 100 := by ring
      have hpowFactor₂ : (n : ℝ) ^ ((yM : ℝ) - (P.hMinus : ℝ)) =
          (n : ℝ) ^ (1 - (P.hPlus : ℝ)) * (n : ℝ) ^ (-(d₂)) := by
        rw [show (yM : ℝ) - (P.hMinus : ℝ) =
          (1 - (P.hPlus : ℝ)) + (-(d₂)) by dsimp [d₂]; ring,
          Real.rpow_add hnR]
      have hpowProd : (n : ℝ) ^ (yM : ℝ) *
          (n : ℝ) ^ (-(P.hMinus : ℝ)) =
          (n : ℝ) ^ ((yM : ℝ) - (P.hMinus : ℝ)) := by
        rw [← Real.rpow_add hnR]
        congr 1 <;> ring
      have hpowA : (n : ℝ) * (n : ℝ) ^ (-(P.hPlus : ℝ)) =
          (n : ℝ) ^ (1 - (P.hPlus : ℝ)) := by
        have hadd := (Real.rpow_add hnR (1 : ℝ) (-(P.hPlus : ℝ))).symm
        simpa [sub_eq_add_neg] using hadd
      have htargetEq : (n : ℝ) * ((n : ℝ) ^ (-(P.hPlus : ℝ)) / 2) / 100 =
          (n : ℝ) ^ (1 - (P.hPlus : ℝ)) / 200 := by
        rw [← hpowA]
        ring
      have hmb : 2 * (P.m n : ℝ) * P.bStar n ≤
          (n : ℝ) * P.aStar n / 100 := by
        have hmul : (P.m n : ℝ) * (n : ℝ) ^ (-(P.hMinus : ℝ)) ≤
            (n : ℝ) ^ (yM : ℝ) * (n : ℝ) ^ (-(P.hMinus : ℝ)) :=
          mul_le_mul_of_nonneg_right hmFloor (by positivity)
        have hscaled := mul_le_mul_of_nonneg_left (le_of_lt hpow₂)
          (show 0 ≤ (n : ℝ) ^ (1 - (P.hPlus : ℝ)) by positivity)
        rw [Params9.bStar, Params9.aStar]
        rw [htargetEq]
        rw [hpowProd, hpowFactor₂] at hmul
        nlinarith [hmul, hscaled]
      simp only [gainMeanSpecialLoss9, hcase]
      nlinarith [hma, hmb]

end HypercubeRamsey.Lane_q_s09_gain2
