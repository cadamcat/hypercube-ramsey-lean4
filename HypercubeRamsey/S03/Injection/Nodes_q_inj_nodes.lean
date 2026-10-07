import HypercubeRamsey.S03.Injection.Comparison
import HypercubeRamsey.Tools.PermConc

/-!
Private random-order estimates for the completion step in Lemma 3.9.
-/

namespace HypercubeRamsey.Lane_q_inj_nodes

open scoped BigOperators

private noncomputable def prefixMass {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (σ : Equiv.Perm (Fin t)) (b : Fin (t + 1)) (y : Fin d) : ℝ :=
  ∑ k : Fin t, if k.val < b.val then q (σ k) y else 0

private theorem uniformPermutation_expect_comp {n : ℕ}
    (e : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin n) → ℝ) :
    (uniformPermutationLaw (ι := Fin n)).expect (fun σ => f (e σ)) =
      (uniformPermutationLaw (ι := Fin n)).expect f := by
  classical
  let P : FinProb (Equiv.Perm (Fin n)) := uniformPermutationLaw (ι := Fin n)
  unfold FinProb.expect
  calc
    _ = ∑ σ, P.w (e σ) * f (e σ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      simp [P, uniformPermutationLaw, FinProb.uniform]
    _ = ∑ σ, P.w σ * f σ := Equiv.sum_comp e (fun σ => P.w σ * f σ)

private theorem expect_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (P : FinProb Ω) (f : ι → Ω → ℝ) :
    P.expect (fun ω => ∑ i, f i ω) = ∑ i, P.expect (f i) := by
  classical
  unfold FinProb.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem uniformPermutation_eval_expect {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (y : Fin d)
    (hpos : 0 < t) (hcol : ∑ i : Fin t, q i y = (t : ℝ) / d)
    (k : Fin t) :
    (uniformPermutationLaw (ι := Fin t)).expect (fun σ => q (σ k) y) = 1 / d := by
  classical
  let P : FinProb (Equiv.Perm (Fin t)) := uniformPermutationLaw (ι := Fin t)
  let m : Fin t → ℝ := fun i => P.expect (fun σ => q (σ i) y)
  have hmeq (i j : Fin t) : m i = m j := by
    let e : Equiv.Perm (Fin t) ≃ Equiv.Perm (Fin t) :=
      Equiv.mulRight (Equiv.swap i j)
    have h := uniformPermutation_expect_comp e (fun σ => q (σ i) y)
    have hfun : (fun σ => q (e σ i) y) = fun σ => q (σ j) y := by
      funext σ
      simp [e, Equiv.mulRight]
    dsimp [m, P]
    rw [hfun] at h
    exact h.symm
  have hsum : (∑ i : Fin t, m i) = ∑ i : Fin t, q i y := by
    calc
      (∑ i : Fin t, m i) = P.expect (fun σ => ∑ i : Fin t, q (σ i) y) := by
        symm
        exact expect_sum P (fun i σ => q (σ i) y)
      _ = P.expect (fun _ => ∑ i : Fin t, q i y) := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro σ hσ
        congr 1
        exact Equiv.sum_comp σ (fun i : Fin t => q i y)
      _ = ∑ i : Fin t, q i y := by
        unfold FinProb.expect
        rw [← Finset.sum_mul, P.sum_eq_one]
        ring
  have hsum' : (∑ i : Fin t, m i) = (t : ℝ) * m k := by
    calc
      _ = ∑ i : Fin t, m k := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hmeq i k
      _ = (t : ℝ) * m k := by simp [Finset.sum_const, nsmul_eq_mul]
  have hmul : (t : ℝ) * m k = (t : ℝ) / d := by
    calc
      (t : ℝ) * m k = ∑ i : Fin t, q i y := hsum'.symm.trans hsum
      _ = (t : ℝ) / d := hcol
  have htne : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpos)
  have hm : m k = 1 / d := by
    apply (mul_left_cancel₀ htne)
    calc
      (t : ℝ) * m k = (t : ℝ) / d := hmul
      _ = (t : ℝ) * (1 / d) := by ring
  exact hm

private theorem prefixMass_expect {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (hpos : 0 < t) (hcol : ∀ y, ∑ i : Fin t, q i y = (t : ℝ) / d)
    (b : Fin (t + 1)) (y : Fin d) :
    (uniformPermutationLaw (ι := Fin t)).expect (fun σ => prefixMass q σ b y) =
      (b.val : ℝ) / d := by
  classical
  have hbt : b.val ≤ t := by omega
  have hcard : ((Finset.univ : Finset (Fin t)).filter (fun k => k.val < b.val)).card = b.val := by
    rw [Fin.card_filter_val_lt]
    exact Nat.min_eq_right hbt
  simp only [prefixMass]
  rw [expect_sum]
  calc
    _ = ∑ k : Fin t, (if k.val < b.val then (1 : ℝ) / d else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkb : k.val < b.val
      · simp [hkb, uniformPermutation_eval_expect q y hpos (hcol y) k]
      · simp [hkb, FinProb.expect]
    _ = (b.val : ℝ) / d := by
      rw [← Finset.sum_filter]
      simp [hcard, Finset.sum_const, nsmul_eq_mul]
      ring

private theorem prefixMass_lipschitz {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (hd : 0 < (d : ℝ))
    (hq0 : ∀ i y, 0 ≤ q i y)
    (hqcap : ∀ i y, q i y ≤ 10 * (d : ℝ) ^ (-(9 / 10 : ℝ)))
    (b : Fin (t + 1)) (y : Fin d) (σ τ : Equiv.Perm (Fin t))
    (hστ : ((Finset.univ : Finset (Fin t)).filter (fun i => σ i ≠ τ i)).card ≤ 2) :
    |prefixMass q σ b y - prefixMass q τ b y| ≤
      20 * (d : ℝ) ^ (-(9 / 10 : ℝ)) := by
  classical
  let A : ℝ := 10 * (d : ℝ) ^ (-(9 / 10 : ℝ))
  let D : Finset (Fin t) := Finset.univ.filter (fun i => σ i ≠ τ i)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hterm (i : Fin t) :
      |(if i.val < b.val then q (σ i) y else 0) -
          (if i.val < b.val then q (τ i) y else 0)| ≤
        if i ∈ D then A else 0 := by
    by_cases hi : i ∈ D
    · have hqσ0 : 0 ≤ q (σ i) y := hq0 _ _
      have hqτ0 : 0 ≤ q (τ i) y := hq0 _ _
      have hqσA : q (σ i) y ≤ A := hqcap _ _
      have hqτA : q (τ i) y ≤ A := hqcap _ _
      have hu0 : 0 ≤ (if i.val < b.val then q (σ i) y else 0) := by
        split_ifs <;> positivity
      have huA : (if i.val < b.val then q (σ i) y else 0) ≤ A := by
        split_ifs <;> simp_all [A]
      have hv0 : 0 ≤ (if i.val < b.val then q (τ i) y else 0) := by
        split_ifs <;> positivity
      have hvA : (if i.val < b.val then q (τ i) y else 0) ≤ A := by
        split_ifs <;> simp_all [A]
      have hdiff :
          |(if i.val < b.val then q (σ i) y else 0) -
            (if i.val < b.val then q (τ i) y else 0)| ≤ A := by
        rw [abs_le]
        constructor <;> nlinarith
      simpa [hi]
    · have hsame : σ i = τ i := by
        by_contra h
        exact hi (by simp [D, h])
      simp [D, hsame]
  calc
    |prefixMass q σ b y - prefixMass q τ b y| =
        |∑ i : Fin t,
          ((if i.val < b.val then q (σ i) y else 0) -
            (if i.val < b.val then q (τ i) y else 0))| := by
          simp only [prefixMass, Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin t,
          |(if i.val < b.val then q (σ i) y else 0) -
            (if i.val < b.val then q (τ i) y else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin t, (if i ∈ D then A else 0) :=
          Finset.sum_le_sum fun i hi => hterm i
    _ = (D.card : ℝ) * A := by
          rw [← Finset.sum_filter]
          simp [D, A, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * A := by
          have hcard : (D.card : ℝ) ≤ 2 := by exact_mod_cast hστ
          exact mul_le_mul_of_nonneg_right hcard hA0
    _ = 20 * (d : ℝ) ^ (-(9 / 10 : ℝ)) := by dsimp [A]; ring

private theorem pr_biUnion_le_sum {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (P : FinProb Ω) (S : Finset ι) (A : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i ∈ S, A i ω) ≤ ∑ i ∈ S, P.pr (A i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert i S hi ih =>
      have hevent :
          (fun ω => ∃ j ∈ insert i S, A j ω) =
            (fun ω => A i ω ∨ ∃ j ∈ S, A j ω) := by
        funext ω
        apply propext
        simp [Finset.mem_insert, hi, or_assoc, or_left_comm, or_comm]
      rw [hevent]
      calc
        P.pr (fun ω => A i ω ∨ ∃ j ∈ S, A j ω) ≤
            P.pr (A i) + P.pr (fun ω => ∃ j ∈ S, A j ω) := FinProb.pr_union_le _ _ _
        _ ≤ P.pr (A i) + ∑ j ∈ S, P.pr (A j) := by
          calc
            P.pr (A i) + P.pr (fun ω => ∃ j ∈ S, A j ω) =
                P.pr (fun ω => ∃ j ∈ S, A j ω) + P.pr (A i) := by ring
            _ ≤ (∑ j ∈ S, P.pr (A j)) + P.pr (A i) := add_le_add_left ih _
            _ = P.pr (A i) + ∑ j ∈ S, P.pr (A j) := by ring
        _ = ∑ j ∈ insert i S, P.pr (A j) := by rw [Finset.sum_insert hi]

private theorem prefix_tail_exponent {d t : ℕ}
    (hd : 1 ≤ (d : ℝ)) (ht : (t : ℝ) ≤ 3 * (d : ℝ) / 4)
    (htpos : 0 < t) :
    (1 / 2 : ℝ) * Real.sqrt (d : ℝ) ≤
      2 * (10 * (d : ℝ) ^ (-(1 / 8 : ℝ))) ^ 2 /
        ((t : ℝ) * (20 * (d : ℝ) ^ (-(9 / 10 : ℝ))) ^ 2) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le (by norm_num) hd
  let δ : ℝ := 10 * (d : ℝ) ^ (-(1 / 8 : ℝ))
  let c : ℝ := 20 * (d : ℝ) ^ (-(9 / 10 : ℝ))
  have hδsq : δ ^ 2 = 100 * (d : ℝ) ^ (-(1 / 4 : ℝ)) := by
    dsimp [δ]
    calc
      (10 * (d : ℝ) ^ (-(1 / 8 : ℝ))) ^ 2 =
          100 * ((d : ℝ) ^ (-(1 / 8 : ℝ))) ^ 2 := by ring
      _ = 100 * (d : ℝ) ^ (-(1 / 8 : ℝ) * 2) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hdpos.le]
        norm_num
      _ = _ := by congr 2 <;> norm_num
  have hcsq : c ^ 2 = 400 * (d : ℝ) ^ (-(9 / 5 : ℝ)) := by
    dsimp [c]
    calc
      (20 * (d : ℝ) ^ (-(9 / 10 : ℝ))) ^ 2 =
          400 * ((d : ℝ) ^ (-(9 / 10 : ℝ))) ^ 2 := by ring
      _ = 400 * (d : ℝ) ^ (-(9 / 10 : ℝ) * 2) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hdpos.le]
        norm_num
      _ = _ := by congr 2 <;> norm_num
  have hpowDen :
      (d : ℝ) * (d : ℝ) ^ (-(9 / 5 : ℝ)) = (d : ℝ) ^ (-(4 / 5 : ℝ)) := by
    calc
      (d : ℝ) * (d : ℝ) ^ (-(9 / 5 : ℝ)) =
          (d : ℝ) ^ (1 : ℝ) * (d : ℝ) ^ (-(9 / 5 : ℝ)) := by simp
      _ = (d : ℝ) ^ ((1 : ℝ) - 9 / 5) := by
        convert (Real.rpow_add hdpos (1 : ℝ) (-(9 / 5 : ℝ))).symm using 1 <;> norm_num
      _ = _ := by congr 1 <;> norm_num
  have hbaseDen :
      (3 * (d : ℝ) / 4) * c ^ 2 = 300 * (d : ℝ) ^ (-(4 / 5 : ℝ)) := by
    rw [hcsq]
    calc
      (3 * (d : ℝ) / 4) * (400 * (d : ℝ) ^ (-(9 / 5 : ℝ))) =
          300 * ((d : ℝ) * (d : ℝ) ^ (-(9 / 5 : ℝ))) := by ring
      _ = _ := by rw [hpowDen]
  have hratio :
      (d : ℝ) ^ (-(1 / 4 : ℝ)) / (d : ℝ) ^ (-(4 / 5 : ℝ)) =
        (d : ℝ) ^ (11 / 20 : ℝ) := by
    have h := (Real.rpow_sub hdpos (-(1 / 4 : ℝ)) (-(4 / 5 : ℝ))).symm
    convert h using 1 <;> norm_num
  have hbaseRatio : 2 * δ ^ 2 / ((3 * (d : ℝ) / 4) * c ^ 2) =
      (2 / 3 : ℝ) * (d : ℝ) ^ (11 / 20 : ℝ) := by
    rw [hδsq, hbaseDen]
    have hp : (0 : ℝ) < (d : ℝ) ^ (-(4 / 5 : ℝ)) := Real.rpow_pos_of_pos hdpos _
    have hq : (0 : ℝ) < (d : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hdpos _
    rw [← hratio]
    field_simp [ne_of_gt hp]
    <;> ring
  have hpow : Real.sqrt (d : ℝ) ≤ (d : ℝ) ^ (11 / 20 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hd (by norm_num)
  have hbase : (1 / 2 : ℝ) * Real.sqrt (d : ℝ) ≤
      (2 / 3 : ℝ) * (d : ℝ) ^ (11 / 20 : ℝ) := by
    have hpow0 : 0 ≤ (d : ℝ) ^ (11 / 20 : ℝ) := Real.rpow_nonneg (by linarith : 0 ≤ (d : ℝ)) _
    nlinarith [hpow, hpow0]
  have htRpos : 0 < (t : ℝ) := by exact_mod_cast htpos
  have δpos : 0 < δ := by dsimp [δ]; positivity
  have cpos : 0 < c := by dsimp [c]; positivity
  have hnum : 0 ≤ 2 * δ ^ 2 := by positivity
  have hdenSmall : 0 < (t : ℝ) * c ^ 2 := mul_pos htRpos (sq_pos_of_pos cpos)
  have hdenCompare : (t : ℝ) * c ^ 2 ≤ (3 * (d : ℝ) / 4) * c ^ 2 :=
    mul_le_mul_of_nonneg_right ht (sq_nonneg c)
  calc
    (1 / 2 : ℝ) * Real.sqrt (d : ℝ) ≤
        2 * δ ^ 2 / ((3 * (d : ℝ) / 4) * c ^ 2) := by rw [hbaseRatio]; exact hbase
    _ ≤ 2 * δ ^ 2 / ((t : ℝ) * c ^ 2) :=
      div_le_div_of_nonneg_left hnum hdenSmall hdenCompare
    _ = 2 * (10 * (d : ℝ) ^ (-(1 / 8 : ℝ))) ^ 2 /
        ((t : ℝ) * (20 * (d : ℝ) ^ (-(9 / 10 : ℝ))) ^ 2) := by
          simp [δ, c]

theorem prefix_order_exists {d t : ℕ}
    (hdNat : 100 ≤ d) (ht : (t : ℝ) ≤ 3 * (d : ℝ) / 4)
    (htpos : 0 < t)
    (q : Fin t → Fin d → ℝ)
    (hq0 : ∀ i y, 0 ≤ q i y)
    (hqcap : ∀ i y, q i y ≤ 10 * (d : ℝ) ^ (-(9 / 10 : ℝ)))
    (hcol : ∀ y, ∑ i : Fin t, q i y = (t : ℝ) / d)
    (hsmall : 2 * (Real.sqrt (d : ℝ)) ^ 4 *
      Real.exp (-(1 / 2 : ℝ) * Real.sqrt (d : ℝ)) < 1) :
    ∃ σ : Equiv.Perm (Fin t), ∀ (b : Fin (t + 1)) (y : Fin d),
      |(∑ k : Fin t, if k.val < b.val then q (σ k) y else 0) -
          (b.val : ℝ) / d| ≤ 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
  classical
  let P : FinProb (Equiv.Perm (Fin t)) := uniformPermutationLaw (ι := Fin t)
  let δ : ℝ := 10 * (d : ℝ) ^ (-(1 / 8 : ℝ))
  let c : ℝ := 20 * (d : ℝ) ^ (-(9 / 10 : ℝ))
  let Index := Fin (t + 1) × Fin d
  let badAt : Index → Equiv.Perm (Fin t) → Prop := fun z σ =>
    δ < |prefixMass q σ z.1 z.2 - (z.1.val : ℝ) / d|
  let bad : Equiv.Perm (Fin t) → Prop := fun σ => ∃ z, badAt z σ
  have hd : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have δpos : 0 < δ := by dsimp [δ]; positivity
  have cpos : 0 < c := by dsimp [c]; positivity
  have hexp := prefix_tail_exponent hd ht htpos
  have hbadAt (z : Index) : P.pr (badAt z) ≤
      2 * Real.exp (-(1 / 2 : ℝ) * Real.sqrt (d : ℝ)) := by
    let f : Equiv.Perm (Fin t) → ℝ := fun σ => prefixMass q σ z.1 z.2
    have hmean : P.expect f = (z.1.val : ℝ) / d := by
      simpa [P, f] using prefixMass_expect q htpos hcol z.1 z.2
    have hlip : ∀ σ τ : Equiv.Perm (Fin t),
        (Finset.univ.filter (fun i : Fin t => σ i ≠ τ i)).card ≤ 2 →
          |f σ - f τ| ≤ c := by
      intro σ τ hστ
      have h := prefixMass_lipschitz q hdpos hq0 hqcap z.1 z.2 σ τ hστ
      simpa [c, f] using h
    have hconc := xPermConc f c δ cpos δpos hlip
    have hconc' : P.pr (fun σ => δ ≤
        |prefixMass q σ z.1 z.2 - (z.1.val : ℝ) / d|) ≤
          2 * Real.exp (-2 * δ ^ 2 / ((t : ℝ) * c ^ 2)) := by
      simpa [P, f, hmean, Fintype.card_fin] using hconc
    have hle : P.pr (badAt z) ≤ P.pr (fun σ => δ ≤
        |prefixMass q σ z.1 z.2 - (z.1.val : ℝ) / d|) := by
      apply FinProb.pr_mono
      intro σ hσ
      exact le_of_lt hσ
    have hexp' : (1 / 2 : ℝ) * Real.sqrt (d : ℝ) ≤
        2 * δ ^ 2 / ((t : ℝ) * c ^ 2) := by
      simpa [δ, c] using hexp
    calc
      P.pr (badAt z) ≤ P.pr (fun σ => δ ≤
          |prefixMass q σ z.1 z.2 - (z.1.val : ℝ) / d|) := hle
      _ ≤ 2 * Real.exp (-2 * δ ^ 2 / ((t : ℝ) * c ^ 2)) := hconc'
      _ ≤ 2 * Real.exp (-(1 / 2 : ℝ) * Real.sqrt (d : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        have hneg := neg_le_neg hexp'
        convert hneg using 1 <;> ring
  have hbadProb : P.pr bad ≤
      (Fintype.card Index : ℝ) *
        (2 * Real.exp (-(1 / 2 : ℝ) * Real.sqrt (d : ℝ))) := by
    calc
      P.pr bad ≤ ∑ z : Index, P.pr (badAt z) := by
        simpa [bad, badAt, Index] using
          pr_biUnion_le_sum P (Finset.univ : Finset Index) badAt
      _ ≤ ∑ z : Index, 2 * Real.exp (-(1 / 2 : ℝ) * Real.sqrt (d : ℝ)) :=
        Finset.sum_le_sum fun z hz => hbadAt z
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have htNat : t + 1 ≤ d := by
    have hd4 : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 4 ≤ d by omega)
    have htR : (t : ℝ) + 1 ≤ (d : ℝ) := by nlinarith [ht, hd4]
    exact_mod_cast htR
  have hcountNat : Fintype.card Index ≤ d * d := by
    simp only [Index, Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_le_mul_right d htNat
  have hcount : (Fintype.card Index : ℝ) ≤ (d : ℝ) ^ 2 := by
    calc
      (Fintype.card Index : ℝ) ≤ ((d * d : ℕ) : ℝ) := by exact_mod_cast hcountNat
      _ = (d : ℝ) ^ 2 := by norm_num [pow_two]
  have hsqrt4 : (d : ℝ) ^ 2 = (Real.sqrt (d : ℝ)) ^ 4 := by
    calc
      (d : ℝ) ^ 2 = ((Real.sqrt (d : ℝ)) ^ 2) ^ 2 := by rw [Real.sq_sqrt (by positivity)]
      _ = _ := by ring
  have hbadLt : P.pr bad < 1 := by
    calc
      P.pr bad ≤ (Fintype.card Index : ℝ) *
          (2 * Real.exp (-(1 / 2 : ℝ) * Real.sqrt (d : ℝ))) := hbadProb
      _ ≤ (d : ℝ) ^ 2 *
          (2 * Real.exp (-(1 / 2 : ℝ) * Real.sqrt (d : ℝ))) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = 2 * (Real.sqrt (d : ℝ)) ^ 4 *
          Real.exp (-(1 / 2 : ℝ) * Real.sqrt (d : ℝ)) := by rw [hsqrt4]; ring
      _ < 1 := hsmall
  have hgood : ∃ σ, ¬ bad σ := by
    by_contra h
    have hall : ∀ σ, bad σ := by
      intro σ
      by_contra hσ
      exact h ⟨σ, hσ⟩
    have hprob : P.pr bad = 1 := by
      calc
        P.pr bad = P.pr (fun _ => True) := by
          congr 1
          funext σ
          simp [hall]
        _ = 1 := by simp [FinProb.pr, P.sum_eq_one]
    linarith
  obtain ⟨σ, hσ⟩ := hgood
  refine ⟨σ, ?_⟩
  intro b y
  have hb : |prefixMass q σ b y - (b.val : ℝ) / d| ≤ δ := by
    by_contra hbound
    apply hσ
    exact ⟨(b, y), by
      change δ < |prefixMass q σ b y - (b.val : ℝ) / d|
      exact lt_of_not_ge hbound⟩
  simpa [prefixMass, δ] using hb

end HypercubeRamsey.Lane_q_inj_nodes
