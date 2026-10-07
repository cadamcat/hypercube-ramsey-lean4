import HypercubeRamsey.S13.ResidualBounds
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.Framework.Embedding
import HypercubeRamsey.S13.Allocation_q_s13_alloc
import HypercubeRamsey.S13.Allocation_sol_s13_allocB
import HypercubeRamsey.S13.Allocation_sol_s13_allocA
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Section 13.3: extraction, type selection, and prefix allocation
-/

namespace HypercubeRamsey.S13

open Filter
open Classical
open scoped BigOperators

/-- P13.3a (sections/13, lines 141–147): direct patch data extracted from a bias witness. -/
def DirectPatchData (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (g : ℕ) : Prop :=
  ∃ (c : Colour) (X Y : Finset (Fin (T.S.N k))),
    X.Nonempty ∧ ∃ hY : Y.Nonempty, X ⊆ RX ∧ Y ⊆ RY ∧ X.card = Y.card ∧
    (1 / 400 : ℝ) * T.S.N k * Real.exp (-(g : ℝ) ^ κ.aB) ≤ X.card ∧
    ∀ x ∈ X, (1 / 2 : ℝ) + g / (4 * T.S.n k) ≤
      deg (T.S.E k) c (Law.unifCore Y hY).w x

/-- L13.0 (sections/13, lines 147–148): exact-size uniform subsampling preserves a finite family
of bounded averages. -/
def UniformSubsampleStatement : Prop :=
  ∀ (N J m n : ℕ) (V : Finset (Fin N)) (f : Fin J → Fin N → ℝ),
    1 ≤ n → m ≤ V.card → n ^ 12 ≤ m →
    J ≤ Nat.ceil (Real.exp (2 * (n : ℝ))) * n ^ 4 →
    (∀ j y, 0 ≤ f j y ∧ f j y ≤ 1) →
    ∃ V' : Finset (Fin N), V' ⊆ V ∧ V'.card = m ∧
      ∀ j, |(∑ y ∈ V', f j y) / m - (∑ y ∈ V, f j y) / V.card| ≤
        (n : ℝ) ^ (-2 : ℝ)

/-- L13.0 (sections/13, lines 244–249): a capped law admits a large uniform approximant for
finitely many bounded tests. -/
def LawSubsampleStatement : Prop :=
  ∀ (N J n : ℕ) (π : Law N) (t : ℝ) (f : Fin J → Fin N → ℝ),
    1 ≤ n → (n : ℝ) ^ 12 ≤ t → (∀ y, t * π.w y ≤ 1) →
    J ≤ Nat.ceil (Real.exp (2 * (n : ℝ))) * n ^ 4 →
    (∀ j y, 0 ≤ f j y ∧ f j y ≤ 1) →
    ∃ V : Finset (Fin N), V.Nonempty ∧
      (∀ y ∈ V, 0 < π.w y) ∧
      (V.card : ℝ) ≥ t / 2 ∧
      ∀ j, |(∑ y ∈ V, f j y) / V.card - π.expect (f j)| ≤ (n : ℝ) ^ (-2 : ℝ)

set_option maxHeartbeats 1000000 in
/-- L13.0a (sections/13, lines 147–148): exact-size sampling with at most exponentially many tests. -/
theorem uniform_subsample : UniformSubsampleStatement := by
  classical
  intro N J m n V f hn hm hmn hJ htests
  have hmpos : 0 < m := by
    have hn12 : 1 ≤ n ^ 12 := Nat.one_le_pow _ _ (by omega)
    omega
  have hVpos : 0 < V.card := lt_of_lt_of_le hmpos hm
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hm
  by_cases hn1 : n = 1
  · subst n
    refine ⟨S, hSsub, hScard, ?_⟩
    intro j
    have hSlo : 0 ≤ ∑ y ∈ S, f j y := by
      apply Finset.sum_nonneg
      intro y hy
      exact (htests j y).1
    have hShi : (∑ y ∈ S, f j y) ≤ (S.card : ℝ) := by
      calc
        _ ≤ ∑ y ∈ S, (1 : ℝ) := Finset.sum_le_sum fun y hy => (htests j y).2
        _ = (S.card : ℝ) := by simp
    have hVlo : 0 ≤ ∑ y ∈ V, f j y := by
      apply Finset.sum_nonneg
      intro y hy
      exact (htests j y).1
    have hVhi : (∑ y ∈ V, f j y) ≤ (V.card : ℝ) := by
      calc
        _ ≤ ∑ y ∈ V, (1 : ℝ) := Finset.sum_le_sum fun y hy => (htests j y).2
        _ = (V.card : ℝ) := by simp
    have hSreal : (S.card : ℝ) = m := by norm_cast
    have hSrealPos : 0 < (S.card : ℝ) := by rw [hSreal]; exact_mod_cast hmpos
    have hSavglo : 0 ≤ (∑ y ∈ S, f j y) / m := div_nonneg hSlo (by positivity)
    have hSavghi : (∑ y ∈ S, f j y) / m ≤ 1 := by
      rw [← hSreal]
      exact (div_le_one hSrealPos).2 hShi
    have hVavglo : 0 ≤ (∑ y ∈ V, f j y) / V.card := div_nonneg hVlo (by positivity)
    have hVavghi : (∑ y ∈ V, f j y) / V.card ≤ 1 :=
      (div_le_one (by exact_mod_cast hVpos)).2 hVhi
    apply abs_le.mpr
    constructor <;> linarith
  · have hn2 : 2 ≤ n := by omega
    have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hDpos : 0 < V.card := hVpos
    have hDreal : 0 < (V.card : ℝ) := by exact_mod_cast hDpos
    have hmD : m ≤ V.card := hm
    let α := {y : Fin N // y ∈ V}
    have hcardα : Fintype.card α = V.card := by simp [α]
    let e : α ≃ Fin V.card := Fintype.equivFinOfCardEq hcardα
    have hcarde : Fintype.card α = V.card := hcardα
    have hmcast : (m : ℝ) ≤ (V.card : ℝ) := by exact_mod_cast hmD
    let K : ℕ := 4 * n ^ 2
    let η : ℝ := 1 / (2 * (n : ℝ) ^ 2)
    have hKpos : 0 < K := by dsimp [K]; positivity
    have hKrealpos : 0 < (K : ℝ) := by exact_mod_cast hKpos
    have hKcast : (K : ℝ) = 4 * (n : ℝ) ^ 2 := by
      dsimp [K]
      norm_num
    have hηpos : 0 < η := by dsimp [η]; positivity
    let f' : Fin J → Fin V.card → ℝ := fun j x => f j (e.symm x).val
    have hf' (j : Fin J) (x : Fin V.card) : 0 ≤ f' j x ∧ f' j x ≤ 1 :=
      htests j _
    let q : Fin J → Fin V.card → ℝ := fun j x =>
      (⌊(K : ℝ) * f' j x⌋₊ : ℝ) / (K : ℝ)
    have hqBounds (j : Fin J) (x : Fin V.card) :
        0 ≤ q j x ∧ q j x ≤ f' j x ∧ f' j x - q j x ≤ 1 / (K : ℝ) := by
      have hfloorNonneg : (0 : ℝ) ≤ (⌊(K : ℝ) * f' j x⌋₊ : ℝ) := by positivity
      have hfloorle : (⌊(K : ℝ) * f' j x⌋₊ : ℝ) ≤ (K : ℝ) * f' j x :=
        Nat.floor_le (mul_nonneg hKrealpos.le (hf' j x).1)
      have hfloorlt : (K : ℝ) * f' j x <
          (⌊(K : ℝ) * f' j x⌋₊ : ℝ) + 1 := by
        simpa only [Nat.cast_succ] using
          (Nat.lt_succ_floor ((K : ℝ) * f' j x))
      have hq0 : 0 ≤ q j x := div_nonneg hfloorNonneg hKrealpos.le
      have hqle : q j x ≤ f' j x :=
        (div_le_iff₀ hKrealpos).2 (by simpa [mul_comm] using hfloorle)
      have herr : f' j x - q j x ≤ 1 / (K : ℝ) := by
        dsimp [q]
        rw [sub_le_iff_le_add]
        rw [← add_div]
        exact (le_div_iff₀ hKrealpos).2 (by simpa [mul_comm, add_comm] using hfloorlt.le)
      exact ⟨hq0, hqle, herr⟩
    let A : Fin J → Fin K → Finset (Fin V.card) := fun j r =>
      Finset.univ.filter fun x => ((r.val + 1 : ℝ) / (K : ℝ)) ≤ f' j x
    let μ : Fin J → Fin K → ℝ := fun j r => (A j r).card / (V.card : ℝ)
    let Acomp : Fin J → Fin K → Finset (Fin V.card) := fun j r => (A j r)ᶜ
    let μcomp : Fin J → Fin K → ℝ := fun j r => (Acomp j r).card / (V.card : ℝ)
    have hAcompAdd (j : Fin J) (r : Fin K) :
        (A j r).card + (Acomp j r).card = V.card := by
      have hUnion : A j r ∪ Acomp j r = Finset.univ := by
        ext x
        by_cases hx : x ∈ A j r
        · simp [hx]
        · simp [Acomp, hx]
      have hdisj : Disjoint (A j r) (Acomp j r) := by
        apply Finset.disjoint_left.mpr
        intro x hx hx'
        have hxnot : x ∉ A j r := by simpa [Acomp] using hx'
        exact hxnot hx
      calc
        _ = (A j r ∪ Acomp j r).card := (Finset.card_union_of_disjoint hdisj).symm
        _ = V.card := by rw [hUnion]; simp
    have hμcomp (j : Fin J) (r : Fin K) : μ j r + μcomp j r = 1 := by
      change (A j r).card / (V.card : ℝ) +
        (Acomp j r).card / (V.card : ℝ) = 1
      have hcast : ((A j r).card : ℝ) + (Acomp j r).card = (V.card : ℝ) := by
        exact_mod_cast hAcompAdd j r
      rw [← add_div, hcast, div_self hDreal.ne']
    let Up : Fin J × Fin K → Finset (Finset (Fin V.card)) := fun p =>
      Finset.univ.filter fun B => B.card = m ∧
        μ p.1 p.2 + η ≤ ((B ∩ A p.1 p.2).card : ℝ) / m
    let Down : Fin J × Fin K → Finset (Finset (Fin V.card)) := fun p =>
      Finset.univ.filter fun B => B.card = m ∧
        μcomp p.1 p.2 + η ≤ ((B ∩ Acomp p.1 p.2).card : ℝ) / m
    have hmrealpos : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have hchoosepos : 0 < Nat.choose V.card m := Nat.choose_pos hmD
    have hchooser : 0 < (Nat.choose V.card m : ℝ) := by exact_mod_cast hchoosepos
    have hrate (j : Fin J) (r : Fin K) :
        ((Up (j, r)).card : ℝ) / (Nat.choose V.card m : ℝ) ≤
          Real.exp (-2 * (m : ℝ) * η ^ 2) := by
      let C := (A j r)
      have hTail := hypergeometric_intersection_tail V.card m hDpos hmpos hmD C
        ((m : ℝ) * η) (by positivity)
      have hμrewrite : (m : ℝ) * μ j r =
          (m : ℝ) * (C.card : ℝ) / (V.card : ℝ) := by
        dsimp [μ, C]
        ring
      have hset : Up (j, r) = Finset.univ.filter (fun B : Finset (Fin V.card) =>
          B.card = m ∧ ((B ∩ C).card : ℝ) ≥
            (m : ℝ) * (C.card : ℝ) / (V.card : ℝ) + (m : ℝ) * η) := by
        ext B
        simp only [Up, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hB, hdev⟩
          refine ⟨hB, ?_⟩
          have hmul := (le_div_iff₀ hmrealpos).mp hdev
          have hmul' : (m : ℝ) * μ j r + (m : ℝ) * η ≤
              (B ∩ A j r).card := by simpa [mul_add, mul_comm] using hmul
          rw [hμrewrite] at hmul'
          simpa [C] using hmul'
        · rintro ⟨hB, hcount⟩
          refine ⟨hB, ?_⟩
          have hmul : (m : ℝ) * (μ j r + η) ≤ (B ∩ C).card := by
            rw [mul_add, hμrewrite]
            simpa [C] using hcount
          exact (le_div_iff₀ hmrealpos).2 (by simpa [mul_comm] using hmul)
      have hrateEq : -(2 * ((m : ℝ) * η) ^ 2) / (m : ℝ) =
          -2 * (m : ℝ) * η ^ 2 := by
        field_simp [ne_of_gt hmrealpos]
        <;> ring
      rw [hset]
      simpa [hrateEq] using hTail
    have hrateComp (j : Fin J) (r : Fin K) :
        ((Down (j, r)).card : ℝ) / (Nat.choose V.card m : ℝ) ≤
          Real.exp (-2 * (m : ℝ) * η ^ 2) := by
      let C := Acomp j r
      have hTail := hypergeometric_intersection_tail V.card m hDpos hmpos hmD C
        ((m : ℝ) * η) (by positivity)
      have hμrewrite : (m : ℝ) * μcomp j r =
          (m : ℝ) * (C.card : ℝ) / (V.card : ℝ) := by
        dsimp [μcomp, C]
        ring
      have hset : Down (j, r) = Finset.univ.filter (fun B : Finset (Fin V.card) =>
          B.card = m ∧ ((B ∩ C).card : ℝ) ≥
            (m : ℝ) * (C.card : ℝ) / (V.card : ℝ) + (m : ℝ) * η) := by
        ext B
        simp only [Down, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hB, hdev⟩
          refine ⟨hB, ?_⟩
          have hmul := (le_div_iff₀ hmrealpos).mp hdev
          have hmul' : (m : ℝ) * μcomp j r + (m : ℝ) * η ≤
              (B ∩ Acomp j r).card := by simpa [mul_add, mul_comm] using hmul
          rw [hμrewrite] at hmul'
          simpa [C] using hmul'
        · rintro ⟨hB, hcount⟩
          refine ⟨hB, ?_⟩
          have hmul : (m : ℝ) * (μcomp j r + η) ≤ (B ∩ C).card := by
            rw [mul_add, hμrewrite]
            simpa [C] using hcount
          exact (le_div_iff₀ hmrealpos).2 (by simpa [mul_comm] using hmul)
      have hrateEq : -(2 * ((m : ℝ) * η) ^ 2) / (m : ℝ) =
          -2 * (m : ℝ) * η ^ 2 := by
        field_simp [ne_of_gt hmrealpos]
        <;> ring
      rw [hset]
      simpa [hrateEq] using hTail
    let idx : Finset (Fin J × Fin K) := Finset.univ
    let bad : Finset (Finset (Fin V.card)) :=
      idx.biUnion fun p => Up p ∪ Down p
    have hbadCard : bad.card ≤ ∑ p ∈ idx, ((Up p).card + (Down p).card) := by
      calc
        _ ≤ ∑ p ∈ idx, (Up p ∪ Down p).card := Finset.card_biUnion_le
        _ ≤ ∑ p ∈ idx, ((Up p).card + (Down p).card) := by
          apply Finset.sum_le_sum
          intro p hp
          exact Finset.card_union_le (Up p) (Down p)
    have hbadReal : (bad.card : ℝ) ≤
        (2 * (J : ℝ) * (K : ℝ)) * (Nat.choose V.card m : ℝ) *
          Real.exp (-2 * (m : ℝ) * η ^ 2) := by
      calc
        _ ≤ ∑ p ∈ idx,
            (((Up p).card : ℝ) + ((Down p).card : ℝ)) := by
          exact_mod_cast hbadCard
        _ ≤ ∑ p ∈ idx, (2 * (Nat.choose V.card m : ℝ) *
            Real.exp (-2 * (m : ℝ) * η ^ 2)) := by
          apply Finset.sum_le_sum
          intro p hp
          rcases p with ⟨j, r⟩
          have hu := hrate j r
          have hd := hrateComp j r
          have huc := (div_le_iff₀ hchooser).mp hu
          have hdc := (div_le_iff₀ hchooser).mp hd
          have huc' : ((Up (j, r)).card : ℝ) ≤
              (Nat.choose V.card m : ℝ) * Real.exp (-2 * (m : ℝ) * η ^ 2) := by
            simpa [mul_comm] using huc
          have hdc' : ((Down (j, r)).card : ℝ) ≤
              (Nat.choose V.card m : ℝ) * Real.exp (-2 * (m : ℝ) * η ^ 2) := by
            simpa [mul_comm] using hdc
          calc
            _ ≤ (Nat.choose V.card m : ℝ) * Real.exp (-2 * (m : ℝ) * η ^ 2) +
                (Nat.choose V.card m : ℝ) * Real.exp (-2 * (m : ℝ) * η ^ 2) :=
              add_le_add huc' hdc'
            _ = _ := by ring
        _ = (2 * (J : ℝ) * (K : ℝ)) * (Nat.choose V.card m : ℝ) *
              Real.exp (-2 * (m : ℝ) * η ^ 2) := by
          simp [idx, Finset.sum_const, Finset.card_univ, Fintype.card_prod]
          ring
    have hceil : (Nat.ceil (Real.exp (2 * (n : ℝ))) : ℝ) ≤
        2 * Real.exp (2 * (n : ℝ)) := by
      have hx : 1 ≤ Real.exp (2 * (n : ℝ)) := by
        have h := Real.add_one_le_exp (2 * (n : ℝ))
        linarith
      have hlt : (Nat.ceil (Real.exp (2 * (n : ℝ))) : ℝ) <
          Real.exp (2 * (n : ℝ)) + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
    have hJreal : (J : ℝ) ≤
        (Nat.ceil (Real.exp (2 * (n : ℝ))) : ℝ) * (n : ℝ) ^ 4 := by
      exact_mod_cast hJ
    have hcoeff : 2 * (J : ℝ) * (K : ℝ) ≤
        16 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 6 := by
      calc
        _ ≤ 2 * ((Nat.ceil (Real.exp (2 * (n : ℝ))) : ℝ) *
            (n : ℝ) ^ 4) * (K : ℝ) := by rw [hKcast]; gcongr
        _ ≤ 2 * (2 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 4) *
            (4 * (n : ℝ) ^ 2) := by rw [hKcast]; gcongr
        _ = 16 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 6 := by ring
    have hetaRate : 2 * (m : ℝ) * η ^ 2 =
        (m : ℝ) / (2 * (n : ℝ) ^ 4) := by
      dsimp [η]
      field_simp
      <;> ring
    have hmnreal : (n : ℝ) ^ 12 ≤ (m : ℝ) := by exact_mod_cast hmn
    have hrateLower : (n : ℝ) ^ 8 / 2 ≤ 2 * (m : ℝ) * η ^ 2 := by
      rw [hetaRate]
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
        (by positivity : (0 : ℝ) < 2 * (n : ℝ) ^ 4)).2
      have hpow : (n : ℝ) ^ 8 * (n : ℝ) ^ 4 = (n : ℝ) ^ 12 := by
        rw [← pow_add]
        <;> norm_num
      nlinarith [hmnreal, hpow]
    have hExpTail : Real.exp (-2 * (m : ℝ) * η ^ 2) ≤
        Real.exp (-((n : ℝ) ^ 8 / 2)) := by
      apply Real.exp_le_exp.mpr
      calc
        -2 * (m : ℝ) * η ^ 2 = -(2 * (m : ℝ) * η ^ 2) := by ring
        _ ≤ -((n : ℝ) ^ 8 / 2) := neg_le_neg hrateLower
    have hExpOne : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      norm_num at h ⊢
      <;> exact h
    have hExpFour : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hExpFourLower : (16 : ℝ) ≤ Real.exp 4 := by
      rw [hExpFour]
      calc
        _ = (2 : ℝ) ^ 4 := by norm_num
        _ ≤ Real.exp 1 ^ 4 := by gcongr
    have hlog16 : Real.log 16 ≤ 4 :=
      (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 16)).2 hExpFourLower
    have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by exact_mod_cast (show 0 < n by omega))
    have hn7 : (16 : ℝ) ≤ (n : ℝ) ^ 7 := by
      have hp : (2 : ℝ) ^ 7 ≤ (n : ℝ) ^ 7 :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnreal 7
      norm_num at hp ⊢
      <;> exact le_trans (by norm_num) hp
    have hn8 : 16 * (n : ℝ) ≤ (n : ℝ) ^ 8 := by
      have hp := mul_le_mul_of_nonneg_left hn7 (by positivity : (0 : ℝ) ≤ n)
      have hpow : (n : ℝ) ^ 7 * (n : ℝ) = (n : ℝ) ^ 8 := by
        simpa [Nat.cast_succ] using (pow_succ (n : ℝ) 7).symm
      calc
        _ = (n : ℝ) * 16 := by ring
        _ ≤ (n : ℝ) * (n : ℝ) ^ 7 := hp
        _ = (n : ℝ) ^ 7 * (n : ℝ) := by ring
        _ = (n : ℝ) ^ 8 := hpow
    have hpoly : 8 * (n : ℝ) - 2 < (n : ℝ) ^ 8 / 2 := by nlinarith [hn8]
    have hlogFactor :
        Real.log (16 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 6) <
          (n : ℝ) ^ 8 / 2 := by
      have hlogs : Real.log (16 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 6) =
          Real.log 16 + 2 * (n : ℝ) + 6 * Real.log (n : ℝ) := by
        rw [show 16 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 6 =
          (16 * Real.exp (2 * (n : ℝ))) * (n : ℝ) ^ 6 by ring,
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) (by positivity), Real.log_exp, Real.log_pow]
        ring
      rw [hlogs]
      linarith
    have hExpFactor :
        16 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 6 <
          Real.exp ((n : ℝ) ^ 8 / 2) :=
      (Real.log_lt_iff_lt_exp (by positivity)).mp hlogFactor
    have hsmall :
        16 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 6 *
          Real.exp (-((n : ℝ) ^ 8 / 2)) < 1 := by
      have hquot :
          (16 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 6) /
            Real.exp ((n : ℝ) ^ 8 / 2) < 1 :=
        (div_lt_one (Real.exp_pos _)).2 hExpFactor
      calc
        _ = (16 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 6) /
            Real.exp ((n : ℝ) ^ 8 / 2) := by
              rw [Real.exp_neg]
              field_simp
              <;> ring
        _ < 1 := hquot
    have hbadFactor : (2 * (J : ℝ) * (K : ℝ)) *
        Real.exp (-2 * (m : ℝ) * η ^ 2) < 1 := by
      calc
        _ ≤ 16 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 6 *
            Real.exp (-2 * (m : ℝ) * η ^ 2) :=
          mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
        _ ≤ 16 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 6 *
            Real.exp (-((n : ℝ) ^ 8 / 2)) :=
          mul_le_mul_of_nonneg_left hExpTail (by positivity)
        _ < 1 := hsmall
    let Samples : Finset (Finset (Fin V.card)) := Finset.univ.powersetCard m
    have hSamplesCard : Samples.card = Nat.choose V.card m := by
      simp [Samples]
    have hbadRealLt : (bad.card : ℝ) < (Nat.choose V.card m : ℝ) := by
      calc
        _ ≤ (2 * (J : ℝ) * (K : ℝ)) *
            (Nat.choose V.card m : ℝ) * Real.exp (-2 * (m : ℝ) * η ^ 2) := hbadReal
        _ = (Nat.choose V.card m : ℝ) *
            ((2 * (J : ℝ) * (K : ℝ)) * Real.exp (-2 * (m : ℝ) * η ^ 2)) := by ring
        _ < (Nat.choose V.card m : ℝ) * 1 :=
          mul_lt_mul_of_pos_left hbadFactor hchooser
        _ = Nat.choose V.card m := by ring
    have hbadLt : bad.card < Samples.card := by
      rw [hSamplesCard]
      exact_mod_cast hbadRealLt
    obtain ⟨B, hBmem, hBnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hbadLt
    have hBcard : B.card = m := (Finset.mem_powersetCard.mp hBmem).2
    have hPartition (j : Fin J) (r : Fin K) :
        (B ∩ A j r).card + (B ∩ Acomp j r).card = m := by
      have hUnion : (B ∩ A j r) ∪ (B ∩ Acomp j r) = B := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact (Finset.mem_inter.mp hx).1
          · exact (Finset.mem_inter.mp hx).1
        · intro hxB
          by_cases hxA : x ∈ A j r
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxB, hxA⟩))
          · exact Finset.mem_union.mpr (Or.inr
              (Finset.mem_inter.mpr ⟨hxB, by simpa [Acomp, hxA]⟩))
      have hdisj : Disjoint (B ∩ A j r) (B ∩ Acomp j r) := by
        apply Finset.disjoint_left.mpr
        intro x hx hx'
        have hxA : x ∈ A j r := (Finset.mem_inter.mp hx).2
        have hxNotA : x ∉ A j r := by
          simpa [Acomp] using (Finset.mem_inter.mp hx').2
        exact hxNotA hxA
      calc
        _ = ((B ∩ A j r) ∪ (B ∩ Acomp j r)).card :=
          (Finset.card_union_of_disjoint hdisj).symm
        _ = B.card := congrArg Finset.card hUnion
        _ = m := hBcard
    have hIndicatorClose (j : Fin J) (r : Fin K) :
        |((B ∩ A j r).card : ℝ) / m - μ j r| ≤ η := by
      have hnotUp : B ∉ Up (j, r) := by
        intro hmem
        apply hBnot
        exact Finset.mem_biUnion.mpr ⟨(j, r), Finset.mem_univ _,
          Finset.mem_union.mpr (Or.inl hmem)⟩
      have hnotDown : B ∉ Down (j, r) := by
        intro hmem
        apply hBnot
        exact Finset.mem_biUnion.mpr ⟨(j, r), Finset.mem_univ _,
          Finset.mem_union.mpr (Or.inr hmem)⟩
      have hnotUpperDev :
          ¬ μ j r + η ≤ ((B ∩ A j r).card : ℝ) / m := by
        intro hdev
        exact hnotUp (by simp [Up, hBcard, hdev])
      have hnotLowerDev :
          ¬ μcomp j r + η ≤ ((B ∩ Acomp j r).card : ℝ) / m := by
        intro hdev
        exact hnotDown (by simp [Down, hBcard, hdev])
      have hcountSum :
          ((B ∩ A j r).card : ℝ) / m + ((B ∩ Acomp j r).card : ℝ) / m = 1 := by
        have hcast : ((B ∩ A j r).card : ℝ) +
            ((B ∩ Acomp j r).card : ℝ) = (m : ℝ) := by
          exact_mod_cast hPartition j r
        rw [← add_div, hcast, div_self hmrealpos.ne']
      have hupper : ((B ∩ A j r).card : ℝ) / m < μ j r + η :=
        lt_of_not_ge hnotUpperDev
      have hlower : μ j r - η < ((B ∩ A j r).card : ℝ) / m := by
        by_contra h
        have hle : ((B ∩ A j r).card : ℝ) / m ≤ μ j r - η := le_of_not_gt h
        have hcompAvg : ((B ∩ Acomp j r).card : ℝ) / m =
            1 - ((B ∩ A j r).card : ℝ) / m := by linarith [hcountSum]
        have hμcomp' : μcomp j r = 1 - μ j r := by linarith [hμcomp j r]
        have hcomp : μcomp j r + η ≤
            ((B ∩ Acomp j r).card : ℝ) / m := by
          rw [hcompAvg, hμcomp']
          linarith
        exact hnotLowerDev hcomp
      apply abs_le.mpr
      constructor <;> linarith
    have hfloorBound (j : Fin J) (x : Fin V.card) :
        ⌊(K : ℝ) * f' j x⌋₊ ≤ K := by
      have hfloorle : (⌊(K : ℝ) * f' j x⌋₊ : ℝ) ≤ (K : ℝ) * f' j x :=
        Nat.floor_le (mul_nonneg hKrealpos.le (hf' j x).1)
      have hprod : (K : ℝ) * f' j x ≤ (K : ℝ) :=
        by
          calc
            _ ≤ (K : ℝ) * 1 := mul_le_mul_of_nonneg_left (hf' j x).2 hKrealpos.le
            _ = (K : ℝ) := by ring
      exact_mod_cast (hfloorle.trans hprod)
    have hThreshold (j : Fin J) (r : Fin K) (x : Fin V.card) :
        ((r.val + 1 : ℝ) / (K : ℝ)) ≤ f' j x ↔
          r.val < ⌊(K : ℝ) * f' j x⌋₊ := by
      rw [div_le_iff₀ hKrealpos]
      rw [Nat.lt_iff_add_one_le,
        Nat.le_floor_iff' (by omega : r.val + 1 ≠ 0)]
      push_cast
      simpa [mul_comm]
    have hThresholdCard (j : Fin J) (x : Fin V.card) :
        (Finset.univ.filter fun r : Fin K => x ∈ A j r).card =
          ⌊(K : ℝ) * f' j x⌋₊ := by
      have hset : (Finset.univ.filter fun r : Fin K => x ∈ A j r) =
          Finset.univ.filter (fun r : Fin K => r.val <
            ⌊(K : ℝ) * f' j x⌋₊) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A]
        exact hThreshold j r x
      rw [hset, Fin.card_filter_val_lt, Nat.min_eq_right (hfloorBound j x)]
    have hqRep (j : Fin J) (x : Fin V.card) :
        q j x =
          (∑ r : Fin K, if x ∈ A j r then (1 : ℝ) else 0) / (K : ℝ) := by
      have hsum : (∑ r : Fin K, if x ∈ A j r then (1 : ℝ) else 0) =
          (⌊(K : ℝ) * f' j x⌋₊ : ℝ) := by
        calc
          _ = ((Finset.univ.filter fun r : Fin K => x ∈ A j r).card : ℝ) := by simp
          _ = _ := by exact_mod_cast hThresholdCard j x
      dsimp [q]
      rw [← hsum]
    have hsumIndicatorB (j : Fin J) (r : Fin K) :
        (∑ x ∈ B, if x ∈ A j r then (1 : ℝ) else 0) =
          (B ∩ A j r).card := by
      calc
        _ = ∑ x ∈ B.filter (fun x => x ∈ A j r), (1 : ℝ) := by
          rw [← Finset.sum_filter]
        _ = (B ∩ A j r).card := by
          have heq : B.filter (fun x => x ∈ A j r) = B ∩ A j r := by
            ext x
            simp
          rw [heq]
          simp
    have hsumIndicatorAll (j : Fin J) (r : Fin K) :
        (∑ x : Fin V.card, if x ∈ A j r then (1 : ℝ) else 0) =
          (A j r).card := by
      calc
        _ = ∑ x ∈ (Finset.univ : Finset (Fin V.card)).filter
            (fun x => x ∈ A j r), (1 : ℝ) := by rw [← Finset.sum_filter]
        _ = (A j r).card := by
          have heq : (Finset.univ : Finset (Fin V.card)).filter
              (fun x => x ∈ A j r) = A j r := by
            ext x
            simp
          rw [heq]
          simp
    have hqSumB (j : Fin J) :
        (∑ x ∈ B, q j x) =
          (∑ r : Fin K, ((B ∩ A j r).card : ℝ)) / (K : ℝ) := by
      calc
        _ = ∑ x ∈ B,
            (∑ r : Fin K, if x ∈ A j r then (1 : ℝ) else 0) / (K : ℝ) := by
              apply Finset.sum_congr rfl
              intro x hx
              exact hqRep j x
        _ = (∑ x ∈ B, ∑ r : Fin K,
            if x ∈ A j r then (1 : ℝ) else 0) / (K : ℝ) := by rw [Finset.sum_div]
        _ = (∑ r : Fin K, ∑ x ∈ B,
            if x ∈ A j r then (1 : ℝ) else 0) / (K : ℝ) := by
              congr 1
              rw [Finset.sum_comm]
        _ = _ := by
          apply congrArg (fun z : ℝ => z / (K : ℝ))
          apply Finset.sum_congr rfl
          intro r hr
          exact hsumIndicatorB j r
    have hqSumAll (j : Fin J) :
        (∑ x : Fin V.card, q j x) =
          (∑ r : Fin K, ((A j r).card : ℝ)) / (K : ℝ) := by
      calc
        _ = ∑ x : Fin V.card,
            (∑ r : Fin K, if x ∈ A j r then (1 : ℝ) else 0) / (K : ℝ) := by
              apply Finset.sum_congr rfl
              intro x hx
              exact hqRep j x
        _ = (∑ x : Fin V.card, ∑ r : Fin K,
            if x ∈ A j r then (1 : ℝ) else 0) / (K : ℝ) := by rw [Finset.sum_div]
        _ = (∑ r : Fin K, ∑ x : Fin V.card,
            if x ∈ A j r then (1 : ℝ) else 0) / (K : ℝ) := by
              congr 1
              rw [Finset.sum_comm]
        _ = _ := by
          apply congrArg (fun z : ℝ => z / (K : ℝ))
          apply Finset.sum_congr rfl
          intro r hr
          exact hsumIndicatorAll j r
    have hsumIndicators (j : Fin J) :
        Finset.univ.sum (fun r : Fin K =>
          ((B ∩ A j r).card : ℝ) / m - (A j r).card / (V.card : ℝ)) =
        (Finset.univ.sum fun r : Fin K => ((B ∩ A j r).card : ℝ)) / m -
          (Finset.univ.sum fun r : Fin K => (A j r).card) / (V.card : ℝ) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
      simp only [Nat.cast_sum]
    have hdivAlgebra (a b : ℝ) :
        (a / (K : ℝ)) / m - (b / (K : ℝ)) / (V.card : ℝ) =
          (1 / (K : ℝ)) * (a / m - b / (V.card : ℝ)) := by
      field_simp [ne_of_gt hKrealpos, ne_of_gt hmrealpos, ne_of_gt hDreal]
      <;> ring
    have hqDiffExact (j : Fin J) :
        (∑ x ∈ B, q j x) / m - (∑ x : Fin V.card, q j x) / (V.card : ℝ) =
          (1 / (K : ℝ)) *
            Finset.univ.sum (fun r : Fin K =>
              ((B ∩ A j r).card : ℝ) / m - (A j r).card / (V.card : ℝ)) := by
      rw [hqSumB, hqSumAll]
      rw [hsumIndicators j]
      simpa [Nat.cast_sum] using
        (hdivAlgebra
          (Finset.univ.sum fun r : Fin K => ((B ∩ A j r).card : ℝ))
          (Finset.univ.sum fun r : Fin K => (A j r).card))
    have hqDiff (j : Fin J) :
        |(∑ x ∈ B, q j x) / m - (∑ x : Fin V.card, q j x) / (V.card : ℝ)| ≤ η := by
      rw [hqDiffExact]
      rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (K : ℝ))]
      have hsumAbs :
          |Finset.univ.sum (fun r : Fin K =>
              ((B ∩ A j r).card : ℝ) / m - (A j r).card / (V.card : ℝ))| ≤
            Finset.univ.sum (fun r : Fin K =>
              |((B ∩ A j r).card : ℝ) / m - (A j r).card / (V.card : ℝ)|) :=
        Finset.abs_sum_le_sum_abs _ _
      have hsumLe :
          Finset.univ.sum (fun r : Fin K =>
            |((B ∩ A j r).card : ℝ) / m - (A j r).card / (V.card : ℝ)|) ≤
            (K : ℝ) * η := by
        calc
          _ ≤ Finset.univ.sum (fun r : Fin K => η) :=
            Finset.sum_le_sum fun r hr => hIndicatorClose j r
          _ = (K : ℝ) * η := by simp
      calc
        (1 / (K : ℝ)) *
            |Finset.univ.sum (fun r : Fin K =>
              ((B ∩ A j r).card : ℝ) / m - (A j r).card / (V.card : ℝ))|
            ≤ (1 / (K : ℝ)) *
              Finset.univ.sum (fun r : Fin K =>
                |((B ∩ A j r).card : ℝ) / m - (A j r).card / (V.card : ℝ)|) :=
          mul_le_mul_of_nonneg_left hsumAbs (by positivity)
        _ ≤ (1 / (K : ℝ)) * ((K : ℝ) * η) :=
          mul_le_mul_of_nonneg_left hsumLe (by positivity)
        _ = η := by field_simp [ne_of_gt hKrealpos]
    have hAvgQError (D : Finset (Fin V.card)) (hD : 0 < D.card) (j : Fin J) :
        |(∑ x ∈ D, f' j x) / D.card - (∑ x ∈ D, q j x) / D.card| ≤
          1 / (K : ℝ) := by
      have hsubNonneg : 0 ≤ ∑ x ∈ D, (f' j x - q j x) := by
        apply Finset.sum_nonneg
        intro x hx
        exact sub_nonneg.mpr (hqBounds j x).2.1
      have hsubLe : (∑ x ∈ D, (f' j x - q j x)) ≤
          (D.card : ℝ) / (K : ℝ) := by
        calc
          _ ≤ ∑ x ∈ D, (1 / (K : ℝ)) :=
            Finset.sum_le_sum fun x hx => (hqBounds j x).2.2
          _ = (D.card : ℝ) / (K : ℝ) := by
            simp [Finset.sum_const, div_eq_mul_inv, mul_comm]
      have hdiff :
          (∑ x ∈ D, f' j x) / D.card - (∑ x ∈ D, q j x) / D.card =
            (∑ x ∈ D, (f' j x - q j x)) / D.card := by
        rw [Finset.sum_sub_distrib, div_sub_div_same]
      rw [hdiff]
      have hratio : 0 ≤
          (∑ x ∈ D, (f' j x - q j x)) / D.card ∧
          (∑ x ∈ D, (f' j x - q j x)) / D.card ≤ 1 / (K : ℝ) := by
        constructor
        · exact div_nonneg hsubNonneg (Nat.cast_nonneg _)
        · calc
            _ ≤ ((D.card : ℝ) / (K : ℝ)) / D.card :=
              div_le_div_of_nonneg_right hsubLe (by exact_mod_cast hD.le)
            _ = 1 / (K : ℝ) := by field_simp [ne_of_gt (by exact_mod_cast hD)]
      exact abs_le.mpr ⟨by linarith [hratio.1], hratio.2⟩
    have hBpos : 0 < B.card := by rw [hBcard]; exact hmpos
    have hunivpos : 0 < (Finset.univ : Finset (Fin V.card)).card := by
      simpa using hDpos
    have hApproxFin (j : Fin J) :
        |(∑ x ∈ B, f' j x) / m -
          (∑ x : Fin V.card, f' j x) / (V.card : ℝ)| ≤ 1 / (n : ℝ) ^ 2 := by
      have hBerr := hAvgQError B hBpos j
      have hUerr := hAvgQError Finset.univ hunivpos j
      have hsumEq :
          (∑ x ∈ B, f' j x) / m - (∑ x : Fin V.card, f' j x) / (V.card : ℝ) =
            ((∑ x ∈ B, f' j x) / m - (∑ x ∈ B, q j x) / m) +
              ((∑ x ∈ B, q j x) / m - (∑ x : Fin V.card, q j x) / (V.card : ℝ)) +
              ((∑ x : Fin V.card, q j x) / (V.card : ℝ) -
                (∑ x : Fin V.card, f' j x) / (V.card : ℝ)) := by ring
      rw [hsumEq]
      let a := (∑ x ∈ B, f' j x) / m - (∑ x ∈ B, q j x) / m
      let b := (∑ x ∈ B, q j x) / m - (∑ x : Fin V.card, q j x) / (V.card : ℝ)
      let c := (∑ x : Fin V.card, q j x) / (V.card : ℝ) -
        (∑ x : Fin V.card, f' j x) / (V.card : ℝ)
      have htriangle : |(a + b) + c| ≤ |a| + |b| + |c| := by
        calc
          _ ≤ |a + b| + |c| := abs_add_le _ _
          _ = |c| + |a + b| := by ring
          _ ≤ |c| + (|a| + |b|) := by nlinarith [abs_add_le a b]
          _ = |a| + |b| + |c| := by ring
      have hBerr' : |a| ≤ 1 / (K : ℝ) := by simpa [a, hBcard] using hBerr
      have hUerr' :
          |c| ≤ 1 / (K : ℝ) := by simpa [c, abs_sub_comm] using hUerr
      calc
        _ ≤ |a| + |b| + |c| := by simpa [a, b, c] using htriangle
        _ ≤ 1 / (K : ℝ) + η + 1 / (K : ℝ) := by
          exact add_le_add (add_le_add hBerr' (hqDiff j)) hUerr'
        _ = 1 / (n : ℝ) ^ 2 := by
          rw [hKcast]
          dsimp [η]
          field_simp
          ring
    let Bα : Finset α := B.image e.symm
    let V' : Finset (Fin N) := Bα.image Subtype.val
    have hV'sub : V' ⊆ V := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
      exact a.property
    have hV'card : V'.card = m := by
      dsimp [V', Bα]
      rw [Finset.card_image_of_injective _ Subtype.val_injective,
        Finset.card_image_of_injective _ e.symm.injective, hBcard]
    have hsumB' (j : Fin J) :
        (∑ y ∈ V', f j y) = ∑ x ∈ B, f' j x := by
      dsimp [V', Bα, f']
      rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h),
        Finset.sum_image (fun _ _ _ _ h => e.symm.injective h)]
    have hsumFull' (j : Fin J) :
        (∑ x : Fin V.card, f' j x) = ∑ y ∈ V, f j y := by
      calc
        _ = ∑ x : α, f j x.val := Equiv.sum_comp e.symm (fun x : α => f j x.val)
        _ = ∑ y ∈ V, f j y := by
          simpa [α] using (Finset.sum_attach V (fun y => f j y))
    refine ⟨V', hV'sub, hV'card, ?_⟩
    intro j
    simpa [hsumB' j, hsumFull' j] using hApproxFin j

private theorem allocation_product_additive_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (X : ∀ i, Ω i → ℝ)
    (hX : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ 1)
    (a t : ℝ) (ha : 0 < a) (hat : a ≤ t)
    (hμpos : 0 < ∑ i, (P i).expect (X i))
    (hμle : ∑ i, (P i).expect (X i) ≤ t) :
    (FinProb.pi P).pr (fun ω => a < |(∑ i, X i (ω i)) - ∑ i, (P i).expect (X i)|) ≤
      2 * Real.exp (-a ^ 2 / (3 * t)) := by
  classical
  let μ : ℝ := ∑ i, (P i).expect (X i)
  let δ : ℝ := a / μ
  have hμpositive : 0 < μ := by simpa [μ] using hμpos
  have hμbound : μ ≤ t := by simpa [μ] using hμle
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδnonneg : 0 ≤ δ := hδpos.le
  have hδμ : δ * μ = a := by
    dsimp [δ]
    field_simp
  have hden : 2 * μ + a ≤ 3 * t := by nlinarith [hμbound, hat]
  have hupperExp : -μ * δ ^ 2 / (2 + δ) ≤ -a ^ 2 / (3 * t) := by
    have hEq : μ * δ ^ 2 / (2 + δ) = a ^ 2 / (2 * μ + a) := by
      dsimp [δ]
      field_simp [ne_of_gt hμpositive]
    have hfrac : a ^ 2 / (3 * t) ≤ a ^ 2 / (2 * μ + a) :=
      div_le_div_of_nonneg_left (sq_nonneg a) (by positivity) hden
    calc
      -μ * δ ^ 2 / (2 + δ) = -(μ * δ ^ 2 / (2 + δ)) := by ring
      _ = -(a ^ 2 / (2 * μ + a)) := by rw [hEq]
      _ ≤ -(a ^ 2 / (3 * t)) := neg_le_neg hfrac
      _ = -a ^ 2 / (3 * t) := by ring
  have hupperRaw := xChernoff_upper P X hX δ hδnonneg
  change (FinProb.pi P).pr
      (fun ω => (1 + δ) * μ ≤ ∑ i, X i (ω i)) ≤
        Real.exp (-μ * δ ^ 2 / (2 + δ)) at hupperRaw
  have hupperThreshold : (1 + δ) * μ = μ + a := by
    calc
      (1 + δ) * μ = μ + δ * μ := by ring
      _ = μ + a := by rw [hδμ]
  have hupper : (FinProb.pi P).pr
      (fun ω => μ + a ≤ ∑ i, X i (ω i)) ≤ Real.exp (-a ^ 2 / (3 * t)) := by
    calc
      _ ≤ Real.exp (-μ * δ ^ 2 / (2 + δ)) := by
        simpa [hupperThreshold] using hupperRaw
      _ ≤ _ := Real.exp_le_exp.mpr hupperExp
  have hlower : (FinProb.pi P).pr
      (fun ω => (∑ i, X i (ω i)) ≤ μ - a) ≤ Real.exp (-a ^ 2 / (3 * t)) := by
    by_cases haμ : a ≤ μ
    · have hδle : δ ≤ 1 := by
        dsimp [δ]
        exact (div_le_one hμpositive).2 haμ
      have hlowerRaw := xChernoff_lower P X hX δ hδnonneg hδle
      change (FinProb.pi P).pr
          (fun ω => (∑ i, X i (ω i)) ≤ (1 - δ) * μ) ≤
            Real.exp (-μ * δ ^ 2 / 2) at hlowerRaw
      have hlowerThreshold : (1 - δ) * μ = μ - a := by
        calc
          (1 - δ) * μ = μ - δ * μ := by ring
          _ = μ - a := by rw [hδμ]
      have hlowerExp : -μ * δ ^ 2 / 2 ≤ -a ^ 2 / (3 * t) := by
        have hEq : μ * δ ^ 2 / 2 = a ^ 2 / (2 * μ) := by
          dsimp [δ]
          field_simp [ne_of_gt hμpositive]
        have hden' : 2 * μ ≤ 3 * t := by nlinarith [hμbound, hat]
        have hfrac : a ^ 2 / (3 * t) ≤ a ^ 2 / (2 * μ) :=
          div_le_div_of_nonneg_left (sq_nonneg a) (by positivity) hden'
        calc
          -μ * δ ^ 2 / 2 = -(μ * δ ^ 2 / 2) := by ring
          _ = -(a ^ 2 / (2 * μ)) := by rw [hEq]
          _ ≤ -(a ^ 2 / (3 * t)) := neg_le_neg hfrac
          _ = -a ^ 2 / (3 * t) := by ring
      calc
        _ ≤ Real.exp (-μ * δ ^ 2 / 2) := by
          simpa [hlowerThreshold] using hlowerRaw
        _ ≤ _ := Real.exp_le_exp.mpr hlowerExp
    · have hμlt : μ < a := lt_of_not_ge haμ
      have hfalse : ∀ ω : ∀ i, Ω i, ¬ (∑ i, X i (ω i) ≤ μ - a) := by
        intro ω hω
        have hnonneg : 0 ≤ ∑ i, X i (ω i) := by
          apply Finset.sum_nonneg
          intro i hi
          exact (hX i (ω i)).1
        linarith
      have hz : (FinProb.pi P).pr (fun ω => (∑ i, X i (ω i)) ≤ μ - a) = 0 := by
        unfold FinProb.pr
        simp [hfalse]
      rw [hz]
      positivity
  have hsplit : ∀ ω : ∀ i, Ω i,
      a < |(∑ i, X i (ω i)) - μ| →
        (μ + a ≤ ∑ i, X i (ω i) ∨ (∑ i, X i (ω i)) ≤ μ - a) := by
    intro ω hω
    by_cases hsign : 0 ≤ (∑ i, X i (ω i)) - μ
    · left
      rw [abs_of_nonneg hsign] at hω
      linarith
    · right
      have hsign' : (∑ i, X i (ω i)) - μ ≤ 0 := le_of_not_ge hsign
      rw [abs_of_nonpos hsign'] at hω
      linarith
  calc
    _ ≤ (FinProb.pi P).pr
        (fun ω => μ + a ≤ (∑ i, X i (ω i)) ∨ (∑ i, X i (ω i)) ≤ μ - a) :=
      FinProb.pr_mono _ _ _ hsplit
    _ ≤ (FinProb.pi P).pr (fun ω => μ + a ≤ ∑ i, X i (ω i)) +
        (FinProb.pi P).pr (fun ω => (∑ i, X i (ω i)) ≤ μ - a) :=
      FinProb.pr_union_le _ _ _
    _ ≤ _ := add_le_add hupper hlower
    _ = 2 * Real.exp (-a ^ 2 / (3 * t)) := by ring

private theorem allocation_pr_finset_exists_le_sum {ι Ω : Type*} [DecidableEq ι]
    [Fintype Ω] (P : FinProb Ω) (B : ι → Ω → Prop) (s : Finset ι) :
    P.pr (fun ω => ∃ i ∈ s, B i ω) ≤ ∑ i ∈ s, P.pr (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert a s ha ih =>
    have heq : (fun ω => ∃ i ∈ insert a s, B i ω) =
        (fun ω => B a ω ∨ ∃ i ∈ s, B i ω) := by
      funext ω
      simp [ha, or_left_comm, or_assoc]
    rw [heq]
    calc
      P.pr (fun ω => B a ω ∨ ∃ i ∈ s, B i ω) ≤
          P.pr (B a) + P.pr (fun ω => ∃ i ∈ s, B i ω) :=
        FinProb.pr_union_le _ _ _
      _ ≤ P.pr (B a) + ∑ i ∈ s, P.pr (B i) :=
        add_le_add_right ih (P.pr (B a))
      _ = ∑ i ∈ insert a s, P.pr (B i) := by simp [ha]

private theorem allocation_pr_exists_le_sum {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] (P : FinProb Ω) (B : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i, B i ω) ≤ ∑ i, P.pr (B i) := by
  simpa using allocation_pr_finset_exists_le_sum P B Finset.univ

private theorem allocation_pr_compl_add {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A : Ω → Prop) : P.pr A + P.pr (fun ω => ¬ A ω) = 1 := by
  classical
  letI : DecidablePred (fun ω : Ω => ¬ A ω) := fun ω => Classical.propDecidable (¬ A ω)
  unfold FinProb.pr
  have hpoint (ω : Ω) :
      (if A ω then P.w ω else 0) + (if ¬ A ω then P.w ω else 0) = P.w ω := by
    by_cases h : A ω <;> simp [h]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ ω, ((if A ω then P.w ω else 0) + (if ¬ A ω then P.w ω else 0))) =
        ∑ ω, P.w ω := by
          apply Finset.sum_congr rfl
          intro ω hω
          exact hpoint ω
    _ = 1 := P.sum_eq_one

private theorem allocation_exists_of_pr_pos {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) (hA : 0 < P.pr A) :
    ∃ ω, A ω ∧ P.w ω ≠ 0 := by
  classical
  by_contra hnone
  have hzero : ∀ ω, A ω → P.w ω = 0 := by
    intro ω hω
    by_contra hωne
    exact hnone ⟨ω, hω, hωne⟩
  have hpr : P.pr A = 0 := by
    unfold FinProb.pr
    apply Finset.sum_eq_zero
    intro ω hω
    by_cases h : A ω
    · simp [h, hzero ω h]
    · simp [h]
  rw [hpr] at hA
  exact (lt_irrefl 0) hA

set_option maxHeartbeats 1000000 in
/-- L13.0b (sections/13, lines 244–249): Bernoulli sampling from the positive support of a capped law. -/
theorem law_subsample : LawSubsampleStatement := by
  classical
  intro N J n π t f hn ht hcap hJ htests
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have htpos : 0 < t := by
    have hp : 0 < (n : ℝ) ^ 12 := by positivity
    exact lt_of_lt_of_le hp ht
  by_cases hn1 : n = 1
  · subst n
    let V : Finset (Fin N) := Finset.univ.filter fun y => π.w y ≠ 0
    have hweight (y : Fin N) : π.w y ≤ 1 / t := by
      apply (le_div_iff₀ htpos).2
      simpa [mul_comm] using hcap y
    have hsumBound : 1 ≤ (V.card : ℝ) / t := by
      calc
        1 = ∑ y, π.w y := π.sum_eq_one.symm
        _ ≤ ∑ y, if y ∈ V then 1 / t else 0 := by
          apply Finset.sum_le_sum
          intro y hy
          by_cases hmem : y ∈ V
          · simpa [hmem] using hweight y
          · have hzero : π.w y = 0 := by
              by_contra hne
              exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
            simp [hmem, hzero]
        _ = ∑ y ∈ V, (1 / t : ℝ) := by rw [← Finset.sum_filter]; simp
        _ = (V.card : ℝ) / t := by simp [div_eq_mul_inv, mul_comm]
    have htcard : t ≤ (V.card : ℝ) := by
      simpa using (le_div_iff₀ htpos).mp hsumBound
    have hVpos : (0 : ℝ) < (V.card : ℝ) := by linarith [ht, htcard]
    have hVcard : 0 < V.card := by exact_mod_cast hVpos
    have hVne : V.Nonempty := Finset.card_pos.mp hVcard
    refine ⟨V, hVne, ?_, ?_, ?_⟩
    · intro y hy
      have hmem : y ∈ V := hy
      have hne : π.w y ≠ 0 := (Finset.mem_filter.mp hmem).2
      exact lt_of_le_of_ne (π.nonneg y) (Ne.symm hne)
    · linarith
    · intro j
      have hsumNonneg : 0 ≤ ∑ y ∈ V, f j y := by
        apply Finset.sum_nonneg
        intro y hy
        exact htests j y |>.1
      have hsumUpper : (∑ y ∈ V, f j y) ≤ (V.card : ℝ) := by
        calc
          _ ≤ ∑ y ∈ V, (1 : ℝ) := Finset.sum_le_sum fun y hy => (htests j y).2
          _ = (V.card : ℝ) := by simp
      have hAvgLower : 0 ≤ (∑ y ∈ V, f j y) / V.card :=
        div_nonneg hsumNonneg (Nat.cast_nonneg _)
      have hAvgUpper : (∑ y ∈ V, f j y) / V.card ≤ 1 :=
        (div_le_one hVpos).2 hsumUpper
      have hπLower : 0 ≤ π.expect (f j) := by
        unfold FinProb.expect
        apply Finset.sum_nonneg
        intro y hy
        exact mul_nonneg (π.nonneg y) (htests j y).1
      have hπUpper : π.expect (f j) ≤ 1 := by
        calc
          π.expect (f j) ≤ π.expect (fun _ => 1) :=
            FinProb.expect_mono π (hfg := fun y => (htests j y).2)
          _ = 1 := FinProb.expect_const π 1
      have herror : |(∑ y ∈ V, f j y) / V.card - π.expect (f j)| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> linarith
      simpa using herror
  · have hn2 : 2 ≤ n := by omega
    let α : ℝ := 1 / t
    let ε : ℝ := 1 / (2 * (n : ℝ) ^ 2 + 2)
    let a : ℝ := ε * t
    have hαpos : 0 < α := by dsimp [α]; positivity
    have hεpos : 0 < ε := by dsimp [ε]; positivity
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hεle : ε ≤ 1 / 2 := by
      dsimp [ε]
      apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).2
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    have hat : a ≤ t := by dsimp [a]; nlinarith
    have ha : 0 < a := by dsimp [a]; positivity
    let G : Fin J → Fin N → ℝ := fun j y => (f j y + α) / (1 + α)
    have hGlow (j : Fin J) (y : Fin N) : α / (1 + α) ≤ G j y := by
      dsimp [G]
      exact div_le_div_of_nonneg_right (by linarith [(htests j y).1]) (by positivity)
    have hGup (j : Fin J) (y : Fin N) : G j y ≤ 1 := by
      dsimp [G]
      exact (div_le_one (by positivity)).2 (by linarith [(htests j y).2])
    let Bern : Fin N → FinProb Bool := fun y =>
      CubeGeometryPToolsCubeR.bernoulliLaw (t * π.w y)
        (mul_nonneg htpos.le (π.nonneg y)) (hcap y)
    let value : Option (Fin J) → Fin N → ℝ := fun q y =>
      match q with
      | none => 1
      | some j => G j y
    let X : Option (Fin J) → Fin N → Bool → ℝ := fun q y b =>
      CubeGeometryPToolsCubeR.boolValue b * value q y
    have hX (q : Option (Fin J)) (y : Fin N) (b : Bool) :
        0 ≤ X q y b ∧ X q y b ≤ 1 := by
      have hb : 0 ≤ CubeGeometryPToolsCubeR.boolValue b ∧
          CubeGeometryPToolsCubeR.boolValue b ≤ 1 := by
        cases b <;> simp [CubeGeometryPToolsCubeR.boolValue]
      have hv : 0 ≤ value q y ∧ value q y ≤ 1 := by
        cases q with
        | none => simp [value]
        | some j => exact ⟨(lt_of_lt_of_le (by positivity) (hGlow j y)).le, hGup j y⟩
      exact ⟨mul_nonneg hb.1 hv.1, mul_le_one₀ hb.2 hv.1 hv.2⟩
    have hBernMean (y : Fin N) : (Bern y).expect CubeGeometryPToolsCubeR.boolValue =
        t * π.w y := by
      simp [Bern, CubeGeometryPToolsCubeR.bernoulliLaw,
        CubeGeometryPToolsCubeR.boolValue, FinProb.expect]
    have hLocal (q : Option (Fin J)) (y : Fin N) :
        (Bern y).expect (X q y) = (t * π.w y) * value q y := by
      simp [FinProb.expect, X, Bern, CubeGeometryPToolsCubeR.bernoulliLaw,
        CubeGeometryPToolsCubeR.boolValue, value]
    let μ : Option (Fin J) → ℝ := fun q => ∑ y, (Bern y).expect (X q y)
    have hMeanNone : μ none = t := by
      dsimp [μ]
      calc
        _ = ∑ y, (t * π.w y) * 1 := by
          apply Finset.sum_congr rfl
          intro y hy
          simpa [value] using hLocal none y
        _ = t * ∑ y, π.w y := by
          simp_rw [mul_one]
          rw [← Finset.mul_sum]
        _ = t := by rw [π.sum_eq_one]; ring
    have hMeanSome (j : Fin J) : μ (some j) = t * π.expect (G j) := by
      dsimp [μ]
      calc
        _ = ∑ y, (t * π.w y) * G j y := by
          apply Finset.sum_congr rfl
          intro y hy
          simpa [value] using hLocal (some j) y
        _ = ∑ y, t * (π.w y * G j y) := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = t * ∑ y, π.w y * G j y := by rw [Finset.mul_sum]
        _ = t * π.expect (G j) := rfl
    have hExpGLower (j : Fin J) : α / (1 + α) ≤ π.expect (G j) := by
      calc
        α / (1 + α) = π.expect (fun _ => α / (1 + α)) :=
          (FinProb.expect_const π _).symm
        _ ≤ π.expect (G j) :=
          FinProb.expect_mono π (hfg := fun y => hGlow j y)
    have hExpGUpper (j : Fin J) : π.expect (G j) ≤ 1 := by
      calc
        π.expect (G j) ≤ π.expect (fun _ => 1) :=
          FinProb.expect_mono π (hfg := fun y => hGup j y)
        _ = 1 := FinProb.expect_const π 1
    have hMeanBounds (q : Option (Fin J)) : 0 < μ q ∧ μ q ≤ t := by
      cases q with
      | none => rw [hMeanNone]; exact ⟨htpos, le_rfl⟩
      | some j =>
        rw [hMeanSome]
        exact ⟨mul_pos htpos (lt_of_lt_of_le (by positivity) (hExpGLower j)),
          by simpa using mul_le_mul_of_nonneg_left (hExpGUpper j) htpos.le⟩
    let P : FinProb (∀ y : Fin N, Bool) := FinProb.pi Bern
    have hTail (q : Option (Fin J)) :
        P.pr (fun ω => a < |(∑ y, X q y (ω y)) - μ q|) ≤
          2 * Real.exp (-a ^ 2 / (3 * t)) := by
      exact allocation_product_additive_tail Bern (fun y => X q y) (fun y b => hX q y b)
        a t ha hat (by simpa [μ] using (hMeanBounds q).1)
          (by simpa [μ] using (hMeanBounds q).2)
    let Bad : (∀ y : Fin N, Bool) → Prop := fun ω =>
      ∃ q : Option (Fin J), a < |(∑ y, X q y (ω y)) - μ q|
    have hFailLe : P.pr Bad ≤ 2 * (J + 1 : ℝ) * Real.exp (-a ^ 2 / (3 * t)) := by
      calc
        P.pr Bad ≤ ∑ q, P.pr (fun ω => a < |(∑ y, X q y (ω y)) - μ q|) :=
          allocation_pr_exists_le_sum P (fun q ω => a < |(∑ y, X q y (ω y)) - μ q|)
        _ ≤ ∑ q : Option (Fin J), 2 * Real.exp (-a ^ 2 / (3 * t)) :=
          Finset.sum_le_sum fun q hq => hTail q
        _ = 2 * (J + 1 : ℝ) * Real.exp (-a ^ 2 / (3 * t)) := by simp; ring
    have hFailLt : P.pr Bad < 1 := by
      have hx : 1 ≤ Real.exp (2 * (n : ℝ)) := by
        have h := Real.add_one_le_exp (2 * (n : ℝ))
        linarith
      have hceillt : (Nat.ceil (Real.exp (2 * (n : ℝ))) : ℝ) <
          Real.exp (2 * (n : ℝ)) + 1 := Nat.ceil_lt_add_one (by positivity)
      have hceil : (Nat.ceil (Real.exp (2 * (n : ℝ))) : ℝ) ≤
          2 * Real.exp (2 * (n : ℝ)) := by linarith
      have hJreal : (J : ℝ) ≤
          (Nat.ceil (Real.exp (2 * (n : ℝ))) : ℝ) * (n : ℝ) ^ 4 := by exact_mod_cast hJ
      have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := by
        have hp : (2 : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 :=
          pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnR 4
        exact le_trans (by norm_num) hp
      have hJplus : (J : ℝ) + 1 ≤
          3 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 4 := by
        calc
          _ ≤ (Nat.ceil (Real.exp (2 * (n : ℝ))) : ℝ) * (n : ℝ) ^ 4 + 1 :=
            add_le_add_left hJreal 1
          _ ≤ 2 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 4 + 1 := by gcongr
          _ ≤ 3 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 4 := by nlinarith
      have hEpsLower : (2 : ℝ) / (5 * (n : ℝ) ^ 2) ≤ ε := by
        dsimp [ε]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith [sq_nonneg ((n : ℝ) - 2)]
      have htR : (n : ℝ) ^ 12 ≤ t := ht
      have hRate : (4 : ℝ) * (n : ℝ) ^ 8 / 75 ≤ a ^ 2 / (3 * t) := by
        have hEpsSq : ((2 : ℝ) / (5 * (n : ℝ) ^ 2)) ^ 2 ≤ ε ^ 2 := by gcongr
        have hA : a ^ 2 / (3 * t) = ε ^ 2 * t / 3 := by
          dsimp [a]
          field_simp [ne_of_gt htpos]
        calc
          (4 : ℝ) * (n : ℝ) ^ 8 / 75 =
              ((2 : ℝ) / (5 * (n : ℝ) ^ 2)) ^ 2 * (n : ℝ) ^ 12 / 3 := by
                field_simp [ne_of_gt hnreal]
                ring
          _ ≤ ε ^ 2 * t / 3 := by gcongr
          _ = a ^ 2 / (3 * t) := hA.symm
      have hlog6 : Real.log 6 < 2 := by
        have hbase : (9 / 8 : ℝ) ≤ Real.exp (1 / 8 : ℝ) := by
          have h := Real.add_one_le_exp (1 / 8 : ℝ)
          norm_num at h ⊢
          exact h
        have hpow : (9 / 8 : ℝ) ^ 8 ≤ Real.exp (1 / 8 : ℝ) ^ 8 := by gcongr
        have hexpOne : Real.exp (1 : ℝ) = Real.exp (1 / 8 : ℝ) ^ 8 := by
          rw [← Real.exp_nat_mul]
          norm_num
        have hsmall : (5 / 2 : ℝ) ≤ Real.exp 1 := by
          have hnum : (5 / 2 : ℝ) ≤ (9 / 8 : ℝ) ^ 8 := by norm_num
          calc
            _ ≤ (9 / 8 : ℝ) ^ 8 := hnum
            _ ≤ Real.exp (1 / 8 : ℝ) ^ 8 := hpow
            _ = Real.exp 1 := hexpOne.symm
        have hexpTwo : 6 < Real.exp 2 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
          nlinarith [sq_nonneg (Real.exp 1 - (5 / 2 : ℝ))]
        exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 6)).2 hexpTwo
      have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by exact_mod_cast (show 0 < n by omega))
      have hn7 : (128 : ℝ) ≤ (n : ℝ) ^ 7 := by
        have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        have hp : (2 : ℝ) ^ 7 ≤ (n : ℝ) ^ 7 := by gcongr
        norm_num at hp
        exact hp
      have hmul : (128 : ℝ) * (n : ℝ) ≤ (n : ℝ) ^ 8 := by
        have h := mul_le_mul_of_nonneg_left hn7 (by positivity : (0 : ℝ) ≤ (n : ℝ))
        nlinarith
      have hpoly : 6 * (n : ℝ) - 2 < (4 : ℝ) * (n : ℝ) ^ 8 / 75 := by nlinarith [hmul]
      have hlogFactor :
          Real.log (6 * (n : ℝ) ^ 4 * Real.exp (2 * (n : ℝ))) <
            (4 : ℝ) * (n : ℝ) ^ 8 / 75 := by
        rw [Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)),
          Real.log_mul (by norm_num : (6 : ℝ) ≠ 0)
            (by positivity : (n : ℝ) ^ 4 ≠ 0), Real.log_pow, Real.log_exp]
        nlinarith [hlog6, hlogn, hpoly]
      have hExpFactor :
          6 * (n : ℝ) ^ 4 * Real.exp (2 * (n : ℝ)) <
            Real.exp ((4 : ℝ) * (n : ℝ) ^ 8 / 75) :=
        (Real.log_lt_iff_lt_exp (by positivity)).mp hlogFactor
      have hsmall : 6 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 4 *
          Real.exp (-((4 : ℝ) * (n : ℝ) ^ 8 / 75)) < 1 := by
        have hquot :
            (6 * (n : ℝ) ^ 4 * Real.exp (2 * (n : ℝ))) /
                Real.exp ((4 : ℝ) * (n : ℝ) ^ 8 / 75) < 1 :=
          (div_lt_one (Real.exp_pos _)).2 hExpFactor
        calc
          _ = (6 * (n : ℝ) ^ 4 * Real.exp (2 * (n : ℝ))) /
              Real.exp ((4 : ℝ) * (n : ℝ) ^ 8 / 75) := by
                rw [Real.exp_neg]
                ring
          _ < 1 := hquot
      have hcoeff : 2 * (J + 1 : ℝ) ≤
          6 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 4 := by
        calc
          _ ≤ 2 * (3 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 4) :=
            mul_le_mul_of_nonneg_left hJplus (by norm_num)
          _ = _ := by ring
      calc
        P.pr Bad ≤ 2 * (J + 1 : ℝ) * Real.exp (-a ^ 2 / (3 * t)) := hFailLe
        _ ≤ 6 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 4 *
            Real.exp (-a ^ 2 / (3 * t)) :=
          mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
        _ ≤ 6 * Real.exp (2 * (n : ℝ)) * (n : ℝ) ^ 4 *
            Real.exp (-((4 : ℝ) * (n : ℝ) ^ 8 / 75)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.mpr
          calc
            -a ^ 2 / (3 * t) = -(a ^ 2 / (3 * t)) := by ring
            _ ≤ -((4 : ℝ) * (n : ℝ) ^ 8 / 75) := neg_le_neg hRate
        _ < 1 := hsmall
    have hGoodPr : 0 < P.pr (fun ω => ¬ Bad ω) := by
      have hcomp := allocation_pr_compl_add P Bad
      linarith
    obtain ⟨ω, hωgood, hωpos⟩ := allocation_exists_of_pr_pos P (fun ω => ¬ Bad ω) hGoodPr
    let V : Finset (Fin N) := Finset.univ.filter fun y => ω y = true
    have hprod : (∏ y, (Bern y).w (ω y)) ≠ 0 := by
      simpa [P, FinProb.pi] using hωpos
    have hfactor (y : Fin N) : (Bern y).w (ω y) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hprod) y (Finset.mem_univ y)
    have hBtrue (y : Fin N) : (Bern y).w true = t * π.w y := by
      simp [Bern, CubeGeometryPToolsCubeR.bernoulliLaw]
    have hVsupport : ∀ y ∈ V, 0 < π.w y := by
      intro y hy
      have hytrue : ω y = true := (Finset.mem_filter.mp hy).2
      have hweight := hfactor y
      rw [hytrue, hBtrue] at hweight
      have hπne : π.w y ≠ 0 := by
        intro hz
        apply hweight
        simp [hz]
      exact lt_of_le_of_ne (π.nonneg y) (Ne.symm hπne)
    have hcount : (∑ y, X none y (ω y)) = (V.card : ℝ) := by
      classical
      simp [X, value, V, CubeGeometryPToolsCubeR.boolValue, Finset.sum_filter]
    have hnotCount : ¬ a < |(V.card : ℝ) - t| := by
      intro hbad
      apply hωgood
      refine ⟨none, ?_⟩
      simpa [hMeanNone, hcount] using hbad
    have hcountDev : |(V.card : ℝ) - t| ≤ a := le_of_not_gt hnotCount
    have hcountLower : t - a ≤ (V.card : ℝ) := by
      have h := (abs_le.mp hcountDev).1
      linarith
    have htHalf : t / 2 ≤ t - a := by
      dsimp [a]
      nlinarith [hεle, htpos.le]
    have hVsize : t / 2 ≤ (V.card : ℝ) := htHalf.trans hcountLower
    have hVpos : 0 < (V.card : ℝ) := by
      have htposHalf : 0 < t / 2 := by positivity
      exact lt_of_lt_of_le htposHalf hVsize
    have hVne : V.Nonempty := by
      exact Finset.card_pos.mp (by exact_mod_cast hVpos)
    have hGoodTest (j : Fin J) :
        |(∑ y, X (some j) y (ω y)) - t * π.expect (G j)| ≤ a := by
      have hnot : ¬ a < |(∑ y, X (some j) y (ω y)) - μ (some j)| := by
        intro hbad
        apply hωgood
        exact ⟨some j, hbad⟩
      have h := le_of_not_gt hnot
      simpa [hMeanSome] using h
    have hsumG (j : Fin J) :
        (∑ y, X (some j) y (ω y)) = ∑ y ∈ V, G j y := by
      classical
      simp [X, value, V, CubeGeometryPToolsCubeR.boolValue, Finset.sum_filter]
    have havgG (j : Fin J) :
        (∑ y ∈ V, G j y) / V.card =
          ((∑ y ∈ V, f j y) / V.card + α) / (1 + α) := by
      have hsum : (∑ y ∈ V, G j y) =
          ((∑ y ∈ V, f j y) + α * (V.card : ℝ)) / (1 + α) := by
        simp only [G]
        rw [← Finset.sum_div, Finset.sum_add_distrib]
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm]
      rw [hsum]
      field_simp [ne_of_gt hVpos, ne_of_gt (by positivity : 0 < 1 + α)]
    have hπG (j : Fin J) :
        π.expect (G j) = (π.expect (f j) + α) / (1 + α) := by
      have hfun : G j = fun y => (1 + α)⁻¹ * (f j y + α) := by
        funext y
        simp [G, div_eq_mul_inv, mul_comm]
      calc
        π.expect (G j) = (1 + α)⁻¹ * π.expect (fun y => f j y + α) := by
          rw [hfun, FinProb.expect_smul]
        _ = (π.expect (f j) + α) / (1 + α) := by
          rw [FinProb.expect_add, FinProb.expect_const]
          ring
    have hGdiff (j : Fin J) :
        |(∑ y ∈ V, f j y) / V.card - π.expect (f j)| =
          (1 + α) * |(∑ y ∈ V, G j y) / V.card - π.expect (G j)| := by
      rw [havgG j, hπG j]
      have hden : 0 < 1 + α := by positivity
      have hinner :
          ((∑ y ∈ V, f j y) / V.card + α) / (1 + α) -
              (π.expect (f j) + α) / (1 + α) =
            ((∑ y ∈ V, f j y) / V.card - π.expect (f j)) / (1 + α) := by
        rw [div_sub_div_same]
        ring
      rw [hinner, abs_div, abs_of_pos hden]
      rw [← mul_div_assoc]
      exact (mul_div_cancel_left₀ _ (ne_of_gt hden)).symm
    have htarget (j : Fin J) :
        |(∑ y ∈ V, f j y) / V.card - π.expect (f j)| ≤ (n : ℝ) ^ (-2 : ℝ) := by
      have hcardreal : (V.card : ℝ) ≥ t - a := by
        exact hcountLower
      have htaPos : 0 < t - a := by
        have hhalf : (1 / 2 : ℝ) ≤ 1 - ε := by linarith
        have hmul := mul_le_mul_of_nonneg_left hhalf htpos.le
        have hhalfprod : t / 2 ≤ t * (1 - ε) := by
          calc
            t / 2 = t * (1 / 2 : ℝ) := by ring
            _ ≤ t * (1 - ε) := hmul
        calc
          t - a = t * (1 - ε) := by dsimp [a]; ring
          _ ≥ t / 2 := hhalfprod
          _ > 0 := by positivity
      have hratio :
          |(∑ y ∈ V, G j y) / V.card - π.expect (G j)| ≤ 2 * a / (t - a) := by
        have hsumdev :
            |(∑ y ∈ V, G j y) - t * π.expect (G j)| ≤ a := by
          simpa only [hsumG j] using hGoodTest j
        have hμrange : 0 ≤ π.expect (G j) ∧ π.expect (G j) ≤ 1 := by
          have hlo : α / (1 + α) ≤ π.expect (G j) := hExpGLower j
          have hhi := hExpGUpper j
          exact ⟨le_trans (by positivity) hlo, hhi⟩
        have hnum :
            |(∑ y ∈ V, G j y) - π.expect (G j) * (V.card : ℝ)| ≤ 2 * a := by
          have hsdiff : |(V.card : ℝ) - t| ≤ a := hcountDev
          have hsecond :
              |π.expect (G j) * (t - (V.card : ℝ))| ≤ a := by
            rw [abs_mul, abs_of_nonneg hμrange.1]
            calc
              _ ≤ 1 * |t - (V.card : ℝ)| :=
                mul_le_mul_of_nonneg_right hμrange.2 (abs_nonneg _)
              _ ≤ a := by simpa [abs_sub_comm] using hsdiff
          have hnumEq :
              (∑ y ∈ V, G j y) - π.expect (G j) * (V.card : ℝ) =
                ((∑ y ∈ V, G j y) - t * π.expect (G j)) +
                  π.expect (G j) * (t - (V.card : ℝ)) := by ring
          calc
            _ = |((∑ y ∈ V, G j y) - t * π.expect (G j)) +
                π.expect (G j) * (t - (V.card : ℝ))| := by rw [hnumEq]
            _ ≤ |(∑ y ∈ V, G j y) - t * π.expect (G j)| +
                |π.expect (G j) * (t - (V.card : ℝ))| := abs_add_le _ _
            _ ≤ a + a := add_le_add hsumdev hsecond
            _ = 2 * a := by ring
        have hratioEq :
            (∑ y ∈ V, G j y) / V.card - π.expect (G j) =
              ((∑ y ∈ V, G j y) - π.expect (G j) * (V.card : ℝ)) / V.card := by
          calc
            _ = (∑ y ∈ V, G j y) / V.card -
                (π.expect (G j) * (V.card : ℝ)) / V.card := by
              rw [mul_div_cancel_right₀ _ (ne_of_gt hVpos)]
            _ = _ := div_sub_div_same _ _ _
        rw [hratioEq, abs_div, abs_of_pos hVpos]
        exact (div_le_div_of_nonneg_right hnum (le_of_lt hVpos)).trans
          (div_le_div_of_nonneg_left (by positivity) htaPos hcardreal)
      have hfinalNum : (1 + α) * (2 * a / (t - a)) ≤ (n : ℝ) ^ (-2 : ℝ) := by
        have hnPow10 : (2 : ℝ) ^ 10 ≤ (n : ℝ) ^ 10 := by gcongr
        have hnPow10' : 2 ≤ (n : ℝ) ^ 10 := by
          calc
            2 ≤ (2 : ℝ) ^ 10 := by norm_num
            _ ≤ (n : ℝ) ^ 10 := hnPow10
        have hnPow : 2 * (n : ℝ) ^ 2 ≤ t := by
          have hmul : 2 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 10 := by
            simpa [mul_comm] using
              mul_le_mul_of_nonneg_left hnPow10' (sq_nonneg (n : ℝ))
          have heq : (n : ℝ) ^ 2 * (n : ℝ) ^ 10 = (n : ℝ) ^ 12 := by
            rw [← pow_add]
          calc
            _ ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 10 := hmul
            _ = (n : ℝ) ^ 12 := heq
            _ ≤ t := ht
        have hta : t - a = t * (1 - ε) := by dsimp [a]; ring
        have h1minus : (0 : ℝ) < 1 - ε := by linarith [hεle]
        let D : ℝ := 2 * (n : ℝ) ^ 2 + 2
        let E : ℝ := 2 * (n : ℝ) ^ 2 + 1
        have hDpos : 0 < D := by dsimp [D]; positivity
        have hEpos : 0 < E := by dsimp [E]; positivity
        have hEpsD : ε * D = 1 := by
          dsimp [ε, D]
          exact one_div_mul_cancel (ne_of_gt (by positivity : (0 : ℝ) < 2 * (n : ℝ) ^ 2 + 2))
        have hEadd : E + 1 = D := by dsimp [D, E]; ring
        have hRatioEps : 2 * ε / (1 - ε) =
            2 / (2 * (n : ℝ) ^ 2 + 1) := by
          have hcross : 2 * ε * E = 2 * (1 - ε) := by
            have hmul : ε * E + ε = 1 := by
              have h := hEpsD
              rw [← hEadd, mul_add, mul_one] at h
              exact h
            nlinarith [hmul]
          apply (div_eq_div_iff (ne_of_gt h1minus) (ne_of_gt hEpos)).2
          simpa [E] using hcross
        have hRatio : 2 * a / (t - a) = 2 * ε / (1 - ε) := by
          apply (div_eq_div_iff (ne_of_gt htaPos) (ne_of_gt h1minus)).2
          rw [hta]
          dsimp [a]
          ring
        have hOnePlus : 1 + α = (t + 1) / t := by
          dsimp [α]
          field_simp [ne_of_gt htpos]
        have hfactor : (1 + α) * (2 * a / (t - a)) =
            2 * (t + 1) / (t * (2 * (n : ℝ) ^ 2 + 1)) := by
          rw [hOnePlus, hRatio, hRatioEps]
          calc
            (t + 1) / t * (2 / (2 * (n : ℝ) ^ 2 + 1)) =
                (t + 1) * 2 / (t * (2 * (n : ℝ) ^ 2 + 1)) :=
              div_mul_div_comm _ _ _ _
            _ = 2 * (t + 1) / (t * (2 * (n : ℝ) ^ 2 + 1)) := by ring
        rw [hfactor, Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
        have hcross : 2 * (t + 1) * (n : ℝ) ^ 2 ≤
            t * (2 * (n : ℝ) ^ 2 + 1) := by nlinarith [hnPow]
        have hcross' : 2 * (t + 1) * (n : ℝ) ^ 2 ≤
            1 * (t * (2 * (n : ℝ) ^ 2 + 1)) := by simpa using hcross
        have hdiv : 2 * (t + 1) / (t * (2 * (n : ℝ) ^ 2 + 1)) ≤
            1 / ((n : ℝ) ^ 2) :=
          (div_le_div_iff₀ (a := 2 * (t + 1))
            (b := t * (2 * (n : ℝ) ^ 2 + 1)) (c := 1) (d := (n : ℝ) ^ 2)
            (by positivity) (by positivity)).2 hcross'
        simpa [one_div] using hdiv
      calc
        _ = (1 + α) * |(∑ y ∈ V, G j y) / V.card - π.expect (G j)| := hGdiff j
        _ ≤ (1 + α) * (2 * a / (t - a)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ ≤ _ := hfinalNum
    refine ⟨V, hVne, hVsupport, hVsize, ?_⟩
    intro j
    exact htarget j

/-- L13.0: assemble the two sampling contracts. -/
theorem random_subset_lemma : UniformSubsampleStatement ∧ LawSubsampleStatement :=
  ⟨uniform_subsample, law_subsample⟩

set_option maxHeartbeats 5000000 in
/-- L13.3a (sections/13, lines 141–147): direct bias extraction from a witness and absence at twice its budget. -/
theorem direct_patch_from_bias (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSampling : UniformSubsampleStatement)
    (hBounds : ResidualScaleBoundFacts κ T) :
    ∀ᶠ k in atTop, ∀ (RX RY : Finset (Fin (T.S.N k))) (g : ℕ),
      RX ⊆ T.X k → RY ⊆ T.Y k →
      (κ.M1 * κ.Q0 ≤ (g : ℝ)) → BiasWitness κ T k RX RY g →
      ¬ BiasWitness κ T k RX RY (2 * g) → DirectPatchData κ T k RX RY g := by
  classical
  have hξpow : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) < 1 := by
    have hz : 0 < 10 * (κ.u : ℝ) + 100 := by positivity
    have hpos : (1 : ℝ) < Real.rpow 2 (10 * (κ.u : ℝ) + 100) :=
      Real.one_lt_rpow (by norm_num) hz
    change (2 : ℝ) ^ (-(10 * (κ.u : ℝ) + 100)) < 1
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ hpos
  have hξsmall : κ.ξ < 1 := by
    have hmul := mul_lt_mul_of_pos_left hξpow hκ.α_rng.1
    have hmul' : κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) < κ.α := by
      simpa using hmul
    have hξα : κ.ξ < κ.α := hκ.ξ_rng.2.trans hmul'
    nlinarith [hκ.α_rng.2]
  have hθsmall : κ.θ < κ.ξ ^ 2 / 3 := by
    have hp : (1 : ℝ) ≤ (4 : ℝ) ^ (κ.u + 3) := one_le_pow₀ (by norm_num)
    have hden : (3 : ℝ) ≤ 3 * (4 : ℝ) ^ (κ.u + 3) := by nlinarith
    have hfrac : κ.ξ ^ 2 / (3 * (4 : ℝ) ^ (κ.u + 3)) ≤ κ.ξ ^ 2 / 3 :=
      div_le_div_of_nonneg_left (sq_nonneg κ.ξ) (by norm_num) hden
    exact hκ.θ_rng.2.trans_le hfrac
  have haPos : 0 < κ.a := by
    rw [hκ.a_eq]
    exact div_pos hκ.θ_rng.1 (by norm_num)
  have haLtOne : κ.a < 1 := by
    rw [hκ.a_eq]
    nlinarith [hθsmall, hξsmall, hκ.ξ_rng.1]
  have hlogArg : (1 : ℝ) < 800 / (κ.a * (1 / 400 : ℝ)) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < κ.a * (1 / 400 : ℝ))).2
    nlinarith [haLtOne]
  have hlogPos : 0 < Real.log (800 / (κ.a * (1 / 400 : ℝ))) := Real.log_pos hlogArg
  have hQ0pos : 0 < κ.Q0 := by
    by_contra hQ0
    have hQ0le : κ.Q0 ≤ 0 := le_of_not_gt hQ0
    have hQCond := hκ.Q0_large 0 hQ0le
    have hzero : Real.rpow (0 : ℝ) κ.aB = 0 := by
      change (0 : ℝ) ^ κ.aB = 0
      exact (Real.rpow_eq_zero (by norm_num : (0 : ℝ) ≤ 0)
        (ne_of_gt hκ.aB_rng.1)).2 rfl
    have hzeroM : Real.rpow (κ.M1 * 0) κ.aB = 0 := by
      calc
        _ = Real.rpow (0 : ℝ) κ.aB := by congr 1 <;> ring
        _ = 0 := hzero
    have hbad := hQCond.1
    rw [hzeroM, mul_zero] at hbad
    linarith [hlogPos]
  have hM1pos : 0 < κ.M1 := by linarith [hκ.M1_big.1]
  have hThresholdPos : 0 < κ.M1 * κ.Q0 := mul_pos hM1pos hQ0pos
  have haBhalf : κ.aB < (1 / 2 : ℝ) := by
    have hmin : min κ.η0 1 ≤ 1 := min_le_right _ _
    have haC : κ.aC < (1 / 10 ^ 6 : ℝ) := by nlinarith [hκ.aC_rng.2, hmin]
    have haB := hκ.aB_rng.2.1
    nlinarith
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hnSeq : Tendsto (fun k : ℕ => (T.S.n k : ℝ) / 4) atTop atTop := by
    have ht := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
    have ht' : Tendsto (fun k : ℕ => (1 / 4 : ℝ) * (T.S.n k : ℝ)) atTop atTop :=
      ht.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 4)
    simpa [div_eq_mul_inv, mul_comm] using ht'
  have hgrowthTendsto := (Real.tendsto_exp_div_pow_atTop 12).comp hnSeq
  have hgrowthEvent : ∀ᶠ k in atTop,
      16 * (4 : ℝ) ^ 12 ≤ Real.exp ((T.S.n k : ℝ) / 4) /
        ((T.S.n k : ℝ) / 4) ^ 12 := by
    have h := hgrowthTendsto.eventually (eventually_ge_atTop (16 * (4 : ℝ) ^ 12))
    filter_upwards [h] with k hk
    exact hk
  have hlarge := T.S.eventually_large 1 16
  have hSampleGrowth : ∀ᶠ k in atTop,
      (T.S.n k : ℝ) ^ 12 ≤
        ((2 : ℝ) ^ T.S.n k * Real.exp (-(T.S.n k : ℝ) / 4)) / 16 := by
    filter_upwards [hlarge, hgrowthEvent] with k hk hg
    have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (by omega : 0 < T.S.n k)
    have hmul :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < ((T.S.n k : ℝ) / 4) ^ 12)).mp hg
    have hcancel : (4 : ℝ) ^ 12 * ((T.S.n k : ℝ) / 4) ^ 12 =
        (T.S.n k : ℝ) ^ 12 := by field_simp [ne_of_gt hnpos] <;> ring
    have hn : (16 : ℝ) * (T.S.n k : ℝ) ^ 12 ≤ Real.exp ((T.S.n k : ℝ) / 4) := by
      calc
        _ = 16 * ((4 : ℝ) ^ 12 * ((T.S.n k : ℝ) / 4) ^ 12) := by rw [hcancel]
        _ = 16 * (4 : ℝ) ^ 12 * ((T.S.n k : ℝ) / 4) ^ 12 := by ring
        _ ≤ Real.exp ((T.S.n k : ℝ) / 4) := hmul
    have htwo : Real.exp ((T.S.n k : ℝ) / 2) ≤ (2 : ℝ) ^ T.S.n k := by
      calc
        Real.exp ((T.S.n k : ℝ) / 2) ≤
            Real.exp ((T.S.n k : ℝ) * Real.log 2) :=
          Real.exp_le_exp.mpr (by nlinarith [hlogTwo])
        _ = (2 : ℝ) ^ T.S.n k := by
          rw [Real.exp_nat_mul]
          simp [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have hsplit : Real.exp ((T.S.n k : ℝ) / 2) *
        Real.exp (-(T.S.n k : ℝ) / 4) = Real.exp ((T.S.n k : ℝ) / 4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hmul := mul_le_mul_of_nonneg_right htwo
      (Real.exp_nonneg (-(T.S.n k : ℝ) / 4))
    rw [hsplit] at hmul
    have hn' : (16 : ℝ) * (T.S.n k : ℝ) ^ 12 ≤
        (2 : ℝ) ^ T.S.n k * Real.exp (-(T.S.n k : ℝ) / 4) := le_trans hn hmul
    have hn'' : (T.S.n k : ℝ) ^ 12 * 16 ≤
        (2 : ℝ) ^ T.S.n k * Real.exp (-(T.S.n k : ℝ) / 4) := by nlinarith [hn']
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2 hn''
  have dens_nonneg_local {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
      (μ ν : Law N) : 0 ≤ dens E c μ ν := by
    classical
    unfold dens
    apply Finset.sum_nonneg
    intro x hx
    apply Finset.sum_nonneg
    intro y hy
    by_cases h : Hits E c x y
    · simp [h]
      exact mul_nonneg (μ.nonneg x) (ν.nonneg y)
    · simp [h]
  have dens_le_one_local {N : ℕ} (E : Fin N → Fin N → Prop) (μ ν : Law N) :
      dens E true μ ν ≤ 1 := by
    have hfalse := dens_nonneg_local E false μ ν
    rw [← dens_add_dens_not E μ ν]
    linarith
  filter_upwards [hlarge, hSampleGrowth] with k hk hsample
  intro RX RY g hRX hRY hg hBias hNo2g
  have hnN : 16 ≤ T.S.n k := hk.1
  have hhost : LargeHost 1 (T.S.n k) (T.S.N k) := hk.2
  have hNlower : (2 : ℝ) ^ T.S.n k ≤ (T.S.N k : ℝ) := by
    simpa [LargeHost] using hhost.1
  rcases hBias with ⟨U, V, hU, hV, hUR, hVR, hUcard, hVcard, hden⟩
  let μU := Law.unifCore U hU
  let μV := Law.unifCore V hV
  let dTrue := dens (T.S.E k) true μU μV
  have hdTrueNonneg : 0 ≤ dTrue := dens_nonneg_local _ _ _ _
  have hdTrueLe : dTrue ≤ 1 := dens_le_one_local _ _ _
  have hdevHalf : |dTrue - 1 / 2| ≤ 1 / 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hgOverN : (g : ℝ) / (T.S.n k : ℝ) ≤ 1 / 2 := le_trans hden hdevHalf
  have hnRealPos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (by omega : 0 < T.S.n k)
  have hgSmall : (g : ℝ) ≤ (T.S.n k : ℝ) / 2 :=
    by simpa [div_eq_mul_inv, mul_comm] using (div_le_iff₀ hnRealPos).mp hgOverN
  have hgposReal : 0 < (g : ℝ) := lt_of_lt_of_le hThresholdPos hg
  have hgpos : 0 < g := by exact_mod_cast hgposReal
  have hGone : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast (by omega : 1 ≤ g)
  have hcolorMargin : ∃ c : Colour,
      (g : ℝ) / (T.S.n k : ℝ) ≤ dens (T.S.E k) c μU μV - 1 / 2 := by
    by_cases htrue : 1 / 2 ≤ dTrue
    · have habs : |dTrue - 1 / 2| = dTrue - 1 / 2 := abs_of_nonneg (by linarith)
      have hden0 : (g : ℝ) / (T.S.n k : ℝ) ≤ |dTrue - 1 / 2| := by
        simpa [dTrue, μU, μV] using hden
      have hden' : (g : ℝ) / (T.S.n k : ℝ) ≤ dTrue - 1 / 2 := by
        calc
          _ ≤ |dTrue - 1 / 2| := hden0
          _ = dTrue - 1 / 2 := habs
      refine ⟨true, ?_⟩
      simpa [dTrue, μU, μV] using hden'
    · have hfalseEq : dens (T.S.E k) false μU μV = 1 - dTrue := by
        have hs := dens_add_dens_not (T.S.E k) μU μV
        change dTrue + dens (T.S.E k) false μU μV = 1 at hs
        linarith
      have habs : |dTrue - 1 / 2| = 1 / 2 - dTrue := by
        rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge htrue))]
        ring
      have hden' := hden
      rw [habs] at hden'
      refine ⟨false, ?_⟩
      rw [hfalseEq]
      linarith [hden']
  obtain ⟨c, hmargin⟩ := hcolorMargin
  have hgPower : Real.rpow (g : ℝ) κ.aB ≤ (T.S.n k : ℝ) / 4 := by
    have hgbase : (0 : ℝ) ≤ (g : ℝ) := (Nat.cast_nonneg _)
    have hnbase : (1 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast (by omega : 1 ≤ T.S.n k)
    have hgn : (g : ℝ) ≤ (T.S.n k : ℝ) := by linarith [hgSmall]
    calc
      Real.rpow (g : ℝ) κ.aB ≤ Real.rpow (T.S.n k : ℝ) κ.aB :=
        Real.rpow_le_rpow hgbase hgn hκ.aB_rng.1.le
      _ ≤ Real.rpow (T.S.n k : ℝ) (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnbase haBhalf.le
      _ = Real.sqrt (T.S.n k : ℝ) := by
        simpa [Real.rpow_eq_pow] using (Real.sqrt_eq_rpow (T.S.n k : ℝ)).symm
      _ ≤ (T.S.n k : ℝ) / 4 := by
        rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ (T.S.n k : ℝ) / 4)]
        have hn16R : (16 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hnN
        nlinarith [sq_nonneg ((T.S.n k : ℝ) - 16)]
  have hExpBudget : Real.exp (-(T.S.n k : ℝ) / 4) ≤
      Real.exp (-(Real.rpow (g : ℝ) κ.aB)) := by
    apply Real.exp_le_exp.mpr
    calc
      -(T.S.n k : ℝ) / 4 = -((T.S.n k : ℝ) / 4) := by ring
      _ ≤ -(Real.rpow (g : ℝ) κ.aB) := neg_le_neg hgPower
  have hsampleLower : (16 : ℝ) * (T.S.n k : ℝ) ^ 12 ≤
      (2 : ℝ) ^ T.S.n k * Real.exp (-(T.S.n k : ℝ) / 4) :=
    by
      have hmul := (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mp hsample
      nlinarith [hmul]
  have hUsize : (16 : ℝ) * (T.S.n k : ℝ) ^ 12 ≤ (U.card : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ T.S.n k * Real.exp (-(T.S.n k : ℝ) / 4) := hsampleLower
      _ ≤ (T.S.N k : ℝ) * Real.exp (-(T.S.n k : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hNlower (Real.exp_nonneg _)
      _ ≤ (T.S.N k : ℝ) * Real.exp (-(Real.rpow (g : ℝ) κ.aB)) :=
        mul_le_mul_of_nonneg_left hExpBudget (Nat.cast_nonneg _)
      _ ≤ (U.card : ℝ) := hUcard
  have hUcardLarge : 16 ≤ U.card := by
    have hnreal16 : (16 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hnN
    have hnOne : (1 : ℝ) ≤ (T.S.n k : ℝ) := by linarith
    have hnPow : (1 : ℝ) ≤ (T.S.n k : ℝ) ^ 12 := one_le_pow₀ hnOne
    have hU16 : (16 : ℝ) ≤ (U.card : ℝ) := by
      have h : (16 : ℝ) ≤ 16 * (T.S.n k : ℝ) ^ 12 := by nlinarith [hnPow]
      exact h.trans hUsize
    exact_mod_cast hU16
  have hHitBounds (x y : Fin (T.S.N k)) :
      0 ≤ hit (T.S.E k) c x y ∧ hit (T.S.E k) c x y ≤ 1 := by
    unfold hit
    split_ifs <;> norm_num
  let score : Fin (T.S.N k) → ℝ := fun x => deg (T.S.E k) c μV.w x
  have hScoreBounds (x : Fin (T.S.N k)) : 0 ≤ score x ∧ score x ≤ 1 := by
    unfold score deg
    constructor
    · apply Finset.sum_nonneg
      intro y hy
      exact mul_nonneg (μV.nonneg y) (hHitBounds x y).1
    · calc
        _ ≤ ∑ y, μV.w y * 1 := Finset.sum_le_sum fun y hy =>
          mul_le_mul_of_nonneg_left (hHitBounds x y).2 (μV.nonneg y)
        _ = ∑ y, μV.w y := by simp
        _ = 1 := μV.sum_eq_one
  have hDensMean (A : Finset (Fin (T.S.N k))) (hA : A.Nonempty) :
      dens (T.S.E k) c (Law.unifCore A hA) μV =
        (∑ x ∈ A, deg (T.S.E k) c μV.w x) / A.card := by
    classical
    have hExp : dens (T.S.E k) c (Law.unifCore A hA) μV =
        ∑ x, (Law.unifCore A hA).w x * deg (T.S.E k) c μV.w x := by
      unfold dens deg hit
      apply Finset.sum_congr rfl
      intro x hx
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    rw [hExp]
    calc
      _ = ∑ x ∈ A, (A.card : ℝ)⁻¹ * deg (T.S.E k) c μV.w x := by
        change (∑ x, (if x ∈ A then (A.card : ℝ)⁻¹ else 0) *
          deg (T.S.E k) c μV.w x) = _
        simp_rw [ite_mul, zero_mul]
        rw [Finset.sum_ite_mem_eq]
      _ = (A.card : ℝ)⁻¹ * ∑ x ∈ A, deg (T.S.E k) c μV.w x := by
        rw [← Finset.mul_sum]
      _ = _ := by
        rw [div_eq_mul_inv]
        ring
  let r : ℕ := U.card / 8
  have hrle : r ≤ U.card := by dsimp [r]; omega
  have hrpos : 0 < r := by dsimp [r]; omega
  let Candidates : Finset (Finset (Fin (T.S.N k))) := U.powersetCard r
  have hCandidates : Candidates.Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    exact hrle
  obtain ⟨U1, hU1mem, hU1max⟩ :=
    Finset.exists_max_image Candidates (fun W => ∑ x ∈ W, score x) hCandidates
  have hU1sub : U1 ⊆ U := (Finset.mem_powersetCard.mp hU1mem).1
  have hU1card : U1.card = r := (Finset.mem_powersetCard.mp hU1mem).2
  have hTopOrder (x : Fin (T.S.N k)) (hx : x ∈ U1)
      (y : Fin (T.S.N k)) (hy : y ∈ U) (hynot : y ∉ U1) : score y ≤ score x := by
    let W := insert y (U1.erase x)
    have hyErase : y ∉ U1.erase x := by simp [hynot]
    have hWsub : W ⊆ U := by
      intro z hz
      rcases Finset.mem_insert.mp hz with hzy | hz
      · simpa [hzy] using hy
      · exact hU1sub (Finset.mem_erase.mp hz).2
    have hWcard : W.card = r := by
      dsimp [W]
      rw [Finset.card_insert_of_notMem hyErase, Finset.card_erase_of_mem hx, hU1card]
      omega
    have hWmem : W ∈ Candidates := Finset.mem_powersetCard.mpr ⟨hWsub, hWcard⟩
    have hmax := hU1max W hWmem
    have hsumErase : (∑ z ∈ U1.erase x, score z) + score x =
        ∑ z ∈ U1, score z := Finset.sum_erase_add U1 score hx
    have hsumW : (∑ z ∈ W, score z) =
        score y + ∑ z ∈ U1.erase x, score z := by
      dsimp [W]
      rw [Finset.sum_insert hyErase]
    rw [hsumW] at hmax
    linarith [hmax, hsumErase]
  have hr400Nat : U.card ≤ 400 * r := by dsimp [r]; omega
  have hr400Real : (U.card : ℝ) ≤ 400 * (r : ℝ) := by exact_mod_cast hr400Nat
  have hrLowerReal : (U.card : ℝ) / 400 ≤ (r : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 400)).2
    simpa [mul_comm] using hr400Real
  have hfactorPos : 0 < Real.rpow 2 κ.aB - 1 := by
    have hpow : 1 < Real.rpow 2 κ.aB := Real.one_lt_rpow (by norm_num) hκ.aB_rng.1
    linarith
  have hpowQ : Real.rpow (κ.M1 * κ.Q0) κ.aB ≤ Real.rpow (g : ℝ) κ.aB :=
    Real.rpow_le_rpow (le_of_lt hThresholdPos) hg hκ.aB_rng.1.le
  have hQCond := hκ.Q0_large κ.Q0 le_rfl
  have hshift : Real.log (800 / (κ.a * (1 / 400 : ℝ))) ≤
      (Real.rpow 2 κ.aB - 1) * Real.rpow (g : ℝ) κ.aB := by
    calc
      _ ≤ (Real.rpow 2 κ.aB - 1) * Real.rpow (κ.M1 * κ.Q0) κ.aB := hQCond.1
      _ ≤ _ := mul_le_mul_of_nonneg_left hpowQ hfactorPos.le
  have hArg400 : (400 : ℝ) ≤ 800 / (κ.a * (1 / 400 : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < κ.a * (1 / 400 : ℝ))).2
    nlinarith [haLtOne]
  have hlog400 : Real.log 400 ≤ Real.log (800 / (κ.a * (1 / 400 : ℝ))) :=
    Real.log_le_log (by norm_num) hArg400
  have h2gPow : Real.rpow (2 * (g : ℝ)) κ.aB =
      Real.rpow 2 κ.aB * Real.rpow (g : ℝ) κ.aB :=
    Real.mul_rpow (by norm_num) (Nat.cast_nonneg g)
  have hgap : Real.rpow (2 * (g : ℝ)) κ.aB - Real.rpow (g : ℝ) κ.aB =
      (Real.rpow 2 κ.aB - 1) * Real.rpow (g : ℝ) κ.aB := by
    rw [h2gPow]
    ring
  have hlogGap : Real.log 400 ≤
      Real.rpow (2 * (g : ℝ)) κ.aB - Real.rpow (g : ℝ) κ.aB :=
    hlog400.trans (hshift.trans_eq hgap.symm)
  have hExpRatio : Real.exp (-(Real.rpow (2 * (g : ℝ)) κ.aB)) ≤
      Real.exp (-(Real.rpow (g : ℝ) κ.aB)) / 400 := by
    have hlogRatio : -(Real.rpow (2 * (g : ℝ)) κ.aB) ≤ Real.log
        (Real.exp (-(Real.rpow (g : ℝ) κ.aB)) / 400) := by
      rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num : (400 : ℝ) ≠ 0),
        Real.log_exp]
      linarith [hlogGap]
    calc
      _ ≤ Real.exp (Real.log
          (Real.exp (-(Real.rpow (g : ℝ) κ.aB)) / 400)) := Real.exp_le_exp.mpr hlogRatio
      _ = _ := Real.exp_log (div_pos (Real.exp_pos _) (by norm_num))
  have hU1Size : (T.S.N k : ℝ) * Real.exp (-(Real.rpow (2 * (g : ℝ)) κ.aB)) ≤
      (U1.card : ℝ) := by
    calc
      _ ≤ (T.S.N k : ℝ) *
          (Real.exp (-(Real.rpow (g : ℝ) κ.aB)) / 400) :=
        mul_le_mul_of_nonneg_left hExpRatio (Nat.cast_nonneg _)
      _ = ((T.S.N k : ℝ) * Real.exp (-(Real.rpow (g : ℝ) κ.aB))) / 400 := by ring
      _ ≤ (U.card : ℝ) / 400 :=
        div_le_div_of_nonneg_right hUcard (by norm_num : (0 : ℝ) ≤ 400)
      _ ≤ (r : ℝ) := hrLowerReal
      _ = (U1.card : ℝ) := by rw [hU1card]
  have hpow2gLower : Real.rpow (g : ℝ) κ.aB ≤ Real.rpow (2 * (g : ℝ)) κ.aB := by
    rw [h2gPow]
    have hpowOne : 1 ≤ Real.rpow 2 κ.aB := (Real.one_lt_rpow (by norm_num) hκ.aB_rng.1).le
    exact (le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg g) _) hpowOne)
  have hV2Size : (T.S.N k : ℝ) * Real.exp (-(Real.rpow (2 * (g : ℝ)) κ.aB)) ≤
      (V.card : ℝ) := by
    calc
      _ ≤ (T.S.N k : ℝ) * Real.exp (-(Real.rpow (g : ℝ) κ.aB)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hpow2gLower))
          (Nat.cast_nonneg _)
      _ ≤ (V.card : ℝ) := hVcard
  have hU1pos : 0 < U1.card := by rw [hU1card]; exact hrpos
  have hU1ne : U1.Nonempty := Finset.card_pos.mp hU1pos
  have hU1abs :
      |dens (T.S.E k) true (Law.unifCore U1 hU1ne) μV - 1 / 2| <
        (2 * g : ℕ) / (T.S.n k : ℝ) := by
    by_contra hnot
    have hdev : (2 * g : ℕ) / (T.S.n k : ℝ) ≤
        |dens (T.S.E k) true (Law.unifCore U1 hU1ne) μV - 1 / 2| := le_of_not_gt hnot
    apply hNo2g
    refine ⟨U1, V, hU1ne, hV, hU1sub.trans hUR, hVR, ?_, ?_, ?_⟩
    · simpa [Nat.cast_mul] using hU1Size
    · simpa [Nat.cast_mul] using hV2Size
    · exact hdev
  have hU1dens : dens (T.S.E k) c (Law.unifCore U1 hU1ne) μV <
      1 / 2 + 2 * (g : ℝ) / (T.S.n k : ℝ) := by
    cases c with
    | true =>
        have h := (abs_lt.mp hU1abs).2
        have hcast : ((2 * g : ℕ) : ℝ) = 2 * (g : ℝ) := by norm_num
        have h' : dens (T.S.E k) true (Law.unifCore U1 hU1ne) μV - 1 / 2 <
            2 * (g : ℝ) / (T.S.n k : ℝ) := by simpa [hcast] using h
        linarith [h']
    | false =>
        have htrueLow :
            1 / 2 - 2 * (g : ℝ) / (T.S.n k : ℝ) <
              dens (T.S.E k) true (Law.unifCore U1 hU1ne) μV := by
          have h := (abs_lt.mp hU1abs).1
          have hcast : ((2 * g : ℕ) : ℝ) = 2 * (g : ℝ) := by norm_num
          rw [hcast] at h
          linarith
        have hsum := dens_add_dens_not (T.S.E k) (Law.unifCore U1 hU1ne) μV
        linarith
  let highThreshold : ℝ := 1 / 2 + (g : ℝ) / (2 * (T.S.n k : ℝ))
  let High : Finset (Fin (T.S.N k)) := U.filter fun x => highThreshold ≤ score x
  have hOutsideLow (hHighSmall : High.card < r) :
      ∀ y ∈ U \ U1, score y < highThreshold := by
    intro y hy
    rcases Finset.mem_sdiff.mp hy with ⟨hyU, hyNotU1⟩
    by_contra hyNotLow
    have hyHigh : y ∈ High := Finset.mem_filter.mpr ⟨hyU, le_of_not_gt hyNotLow⟩
    have hInterSmall : (High ∩ U1).card < U1.card := by
      have hInterCard : (High ∩ U1).card ≤ High.card :=
        Finset.card_le_card Finset.inter_subset_left
      rw [hU1card]
      omega
    obtain ⟨x, hxU1, hxNotInter⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hInterSmall
    have hxNotHigh : x ∉ High := by
      intro hxHigh
      exact hxNotInter (Finset.mem_inter.mpr ⟨hxHigh, hxU1⟩)
    have hxLow : score x < highThreshold := by
      apply lt_of_not_ge
      intro hxHigh
      exact hxNotHigh (Finset.mem_filter.mpr ⟨hU1sub hxU1, hxHigh⟩)
    have horder := hTopOrder x hxU1 y hyU hyNotU1
    linarith
  let Uout : Finset (Fin (T.S.N k)) := U \ U1
  have hUunion : U1 ∪ Uout = U := by
    ext x
    by_cases hx : x ∈ U
    · by_cases hx1 : x ∈ U1
      · simp [Uout, hx, hx1]
      · simp [Uout, hx, hx1]
    · have hx1 : x ∉ U1 := fun hx1 => hx (hU1sub hx1)
      simp [Uout, hx, hx1]
  have hUdisj : Disjoint U1 Uout := by
    apply Finset.disjoint_left.mpr
    intro x hx hxout
    exact (Finset.mem_sdiff.mp hxout).2 hx
  have hUoutCard : Uout.card = U.card - r := by
    dsimp [Uout]
    rw [Finset.card_sdiff_of_subset hU1sub, hU1card]
  have hUoutCast : (Uout.card : ℝ) = (U.card : ℝ) - (r : ℝ) := by
    rw [hUoutCard, Nat.cast_sub hrle]
  have hUPos : 0 < U.card := Finset.card_pos.mpr hU
  have hUPosReal : 0 < (U.card : ℝ) := by exact_mod_cast hUPos
  have hrPosReal : 0 < (r : ℝ) := by exact_mod_cast hrpos
  have hdelta : 0 < (g : ℝ) / (T.S.n k : ℝ) := div_pos hgposReal hnRealPos
  have hU1Sum : (∑ x ∈ U1, score x) =
      (r : ℝ) * dens (T.S.E k) c (Law.unifCore U1 hU1ne) μV := by
    have hmean := hDensMean U1 hU1ne
    have hmean' : dens (T.S.E k) c (Law.unifCore U1 hU1ne) μV =
        (∑ x ∈ U1, score x) / (r : ℝ) := by
      simpa [score, hU1card] using hmean
    rw [hmean']
    field_simp [ne_of_gt hrPosReal]
  have hUoutSum (hHighSmall : High.card < r) : (∑ x ∈ Uout, score x) ≤
      (Uout.card : ℝ) * highThreshold := by
    calc
      _ ≤ ∑ x ∈ Uout, highThreshold :=
        Finset.sum_le_sum fun x hx => by
          have hx' : x ∈ U \ U1 := by simpa [Uout] using hx
          exact (hOutsideLow hHighSmall x hx').le
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hDensU : dens (T.S.E k) c μU μV =
      (∑ x ∈ U, score x) / (U.card : ℝ) := by
    simpa [μU, score] using hDensMean U hU
  have hSumSplit : (∑ x ∈ U, score x) =
      (∑ x ∈ U1, score x) + (∑ x ∈ Uout, score x) := by
    calc
      _ = ∑ x ∈ U1 ∪ Uout, score x := by rw [hUunion]
      _ = _ := Finset.sum_union hUdisj
  let p : ℝ := (r : ℝ) / (U.card : ℝ)
  have hp0 : 0 ≤ p := div_nonneg hrPosReal.le hUPosReal.le
  have h8r : 8 * r ≤ U.card := by
    dsimp [r]
    omega
  have hpLe : p ≤ 1 / 8 := by
    change (r : ℝ) / (U.card : ℝ) ≤ 1 / 8
    apply (div_le_iff₀ hUPosReal).2
    have h8rR : (8 : ℝ) * (r : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast h8r
    nlinarith
  have hUoutAvg : (Uout.card : ℝ) / (U.card : ℝ) = 1 - p := by
    rw [hUoutCast]
    change ((U.card : ℝ) - (r : ℝ)) / (U.card : ℝ) =
      1 - (r : ℝ) / (U.card : ℝ)
    rw [sub_div, div_self (ne_of_gt hUPosReal)]
  have hDensUUpper (hHighSmall : High.card < r) : dens (T.S.E k) c μU μV ≤
      p * dens (T.S.E k) c (Law.unifCore U1 hU1ne) μV +
        (1 - p) * highThreshold := by
    rw [hDensU, hSumSplit]
    calc
      _ ≤ ((r : ℝ) * dens (T.S.E k) c (Law.unifCore U1 hU1ne) μV +
          (Uout.card : ℝ) * highThreshold) / (U.card : ℝ) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hUPosReal)
        exact add_le_add hU1Sum.le (hUoutSum hHighSmall)
      _ = _ := by
        rw [add_div]
        have hfirst : (r : ℝ) * dens (T.S.E k) c (Law.unifCore U1 hU1ne) μV /
            (U.card : ℝ) = p * dens (T.S.E k) c (Law.unifCore U1 hU1ne) μV := by
          dsimp only [p]
          ring
        have hsecond : (Uout.card : ℝ) * highThreshold / (U.card : ℝ) =
            (1 - p) * highThreshold := by
          rw [← hUoutAvg]
          ring
        rw [hfirst, hsecond]
  have hXY : highThreshold ≤ 1 / 2 + 2 * (g : ℝ) / (T.S.n k : ℝ) := by
    dsimp [highThreshold]
    have hfrac : (g : ℝ) / (2 * (T.S.n k : ℝ)) ≤
        2 * (g : ℝ) / (T.S.n k : ℝ) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (T.S.n k : ℝ))
        hnRealPos).2
      nlinarith [mul_nonneg (le_of_lt hgposReal) (le_of_lt hnRealPos)]
    linarith
  have hU1upper : dens (T.S.E k) c (Law.unifCore U1 hU1ne) μV ≤
      1 / 2 + 2 * (g : ℝ) / (T.S.n k : ℝ) := hU1dens.le
  have hweight :
      p * (1 / 2 + 2 * (g : ℝ) / (T.S.n k : ℝ)) +
        (1 - p) * highThreshold ≤
      (1 / 8) * (1 / 2 + 2 * (g : ℝ) / (T.S.n k : ℝ)) +
        (1 - (1 / 8 : ℝ)) * highThreshold := by
    have hprod := mul_nonneg (sub_nonneg.mpr hpLe) (sub_nonneg.mpr hXY)
    nlinarith [hprod]
  have hDensUUpperFinal (hHighSmall : High.card < r) : dens (T.S.E k) c μU μV ≤
      1 / 2 + (11 / 16 : ℝ) * ((g : ℝ) / (T.S.n k : ℝ)) := by
    calc
      _ ≤ p * dens (T.S.E k) c (Law.unifCore U1 hU1ne) μV +
          (1 - p) * highThreshold := hDensUUpper hHighSmall
      _ ≤ p * (1 / 2 + 2 * (g : ℝ) / (T.S.n k : ℝ)) +
          (1 - p) * highThreshold := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hU1upper hp0
        · exact le_rfl
      _ ≤ (1 / 8) * (1 / 2 + 2 * (g : ℝ) / (T.S.n k : ℝ)) +
          (1 - (1 / 8 : ℝ)) * highThreshold := hweight
      _ = 1 / 2 + (11 / 16 : ℝ) * ((g : ℝ) / (T.S.n k : ℝ)) := by
        dsimp [highThreshold]
        ring
  have hHighCard : r ≤ High.card := by
    by_contra hnot
    have hHighSmall : High.card < r := lt_of_not_ge hnot
    linarith [hmargin, hDensUUpperFinal hHighSmall, hdelta]
  have hVsize : 16 * (T.S.n k : ℝ) ^ 12 ≤ (V.card : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ T.S.n k * Real.exp (-(T.S.n k : ℝ) / 4) := hsampleLower
      _ ≤ (T.S.N k : ℝ) * Real.exp (-(T.S.n k : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hNlower (Real.exp_nonneg _)
      _ ≤ (T.S.N k : ℝ) * Real.exp (-(Real.rpow (g : ℝ) κ.aB)) :=
        mul_le_mul_of_nonneg_left hExpBudget (Nat.cast_nonneg _)
      _ ≤ (V.card : ℝ) := hVcard
  have hUsizeNat : 16 * (T.S.n k) ^ 12 ≤ U.card := by exact_mod_cast hUsize
  have hVsizeNat : 16 * (T.S.n k) ^ 12 ≤ V.card := by exact_mod_cast hVsize
  have hrSmall : (T.S.n k) ^ 12 ≤ r := by
    dsimp [r]
    omega
  have hVSmall : (T.S.n k) ^ 12 ≤ V.card := by omega
  let m : ℕ := min r V.card
  have hmSmall : (T.S.n k) ^ 12 ≤ m := by
    dsimp [m]
    exact le_min hrSmall hVSmall
  have hmV : m ≤ V.card := Nat.min_le_right _ _
  have hmHigh : m ≤ High.card := (Nat.min_le_left _ _).trans hHighCard
  obtain ⟨X, hXsub, hXcard⟩ := Finset.exists_subset_card_eq hmHigh
  have hmPos : 0 < m := by
    have hn12 : 0 < (T.S.n k) ^ 12 := Nat.pow_pos (by omega)
    omega
  have hXne : X.Nonempty := Finset.card_pos.mp (by rw [hXcard]; exact hmPos)
  let scale : ℝ := (1 / 400 : ℝ) * (T.S.N k : ℝ) *
    Real.exp (-(Real.rpow (g : ℝ) κ.aB))
  have hscaleR : scale ≤ (r : ℝ) := by
    calc
      _ = ((T.S.N k : ℝ) * Real.exp (-(Real.rpow (g : ℝ) κ.aB))) / 400 := by
        dsimp [scale]
        ring
      _ ≤ (U.card : ℝ) / 400 :=
        div_le_div_of_nonneg_right hUcard (by norm_num : (0 : ℝ) ≤ 400)
      _ ≤ (r : ℝ) := hrLowerReal
  have hscaleV : scale ≤ (V.card : ℝ) := by
    calc
      _ = ((T.S.N k : ℝ) * Real.exp (-(Real.rpow (g : ℝ) κ.aB))) / 400 := by
        dsimp [scale]
        ring
      _ ≤ (T.S.N k : ℝ) * Real.exp (-(Real.rpow (g : ℝ) κ.aB)) :=
        div_le_self (by positivity) (by norm_num)
      _ ≤ (V.card : ℝ) := hVcard
  have hscaleM : scale ≤ (m : ℝ) := by
    rw [show (m : ℝ) = min (r : ℝ) (V.card : ℝ) by simp [m]]
    exact le_min hscaleR hscaleV
  have hexpNat : Real.exp (T.S.n k : ℝ) = Real.exp 1 ^ T.S.n k := by
    rw [show (T.S.n k : ℝ) = (T.S.n k : ℝ) * 1 by ring,
      Real.exp_nat_mul]
  have hpowExp : (2 : ℝ) ^ T.S.n k ≤ Real.exp (2 * (T.S.n k : ℝ)) := by
    calc
      _ ≤ Real.exp 1 ^ T.S.n k := by
        gcongr
        exact Real.exp_one_gt_two.le
      _ = Real.exp (T.S.n k : ℝ) := hexpNat.symm
      _ ≤ Real.exp (2 * (T.S.n k : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith [hnRealPos])
  have hpowCeil : 2 ^ T.S.n k ≤ Nat.ceil (Real.exp (2 * (T.S.n k : ℝ))) := by
    have h : (2 : ℝ) ^ T.S.n k ≤
        (Nat.ceil (Real.exp (2 * (T.S.n k : ℝ))) : ℝ) :=
      hpowExp.trans (Nat.le_ceil _)
    exact_mod_cast h
  have hnPow : T.S.n k ≤ (T.S.n k) ^ 4 := by
    calc
      _ = T.S.n k * 1 := by omega
      _ ≤ T.S.n k * (T.S.n k) ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.one_le_pow 3 _ (by omega))
      _ = (T.S.n k) ^ 4 := by ring
  have hJbound : X.card ≤ Nat.ceil (Real.exp (2 * (T.S.n k : ℝ))) * (T.S.n k) ^ 4 := by
    rw [hXcard]
    calc
      _ ≤ T.S.N k := by
        have hUcardN : U.card ≤ T.S.N k := by simpa using (Finset.card_le_univ U)
        exact (Nat.min_le_left _ _).trans (hrle.trans hUcardN)
      _ ≤ T.S.n k * 2 ^ T.S.n k := hhost.2
      _ ≤ T.S.n k * Nat.ceil (Real.exp (2 * (T.S.n k : ℝ))) :=
        Nat.mul_le_mul_left _ hpowCeil
      _ ≤ (T.S.n k) ^ 4 * Nat.ceil (Real.exp (2 * (T.S.n k : ℝ))) :=
        Nat.mul_le_mul_right _ hnPow
      _ = _ := Nat.mul_comm _ _
  let eX : {x : Fin (T.S.N k) // x ∈ X} ≃ Fin X.card :=
    Fintype.equivFinOfCardEq (by simp)
  let tests : Fin X.card → Fin (T.S.N k) → ℝ :=
    fun j y => hit (T.S.E k) c (eX.symm j).val y
  have htests (j : Fin X.card) (y : Fin (T.S.N k)) :
      0 ≤ tests j y ∧ tests j y ≤ 1 := by
    dsimp [tests]
    exact hHitBounds _ _
  obtain ⟨Y, hYsub, hYcard, happrox⟩ :=
    hSampling (T.S.N k) X.card m (T.S.n k) V tests (by omega) hmV hmSmall hJbound htests
  have hYne : Y.Nonempty := Finset.card_pos.mp (by rw [hYcard]; exact hmPos)
  have hHighSubsetU : High ⊆ U := by
    intro x hx
    simp only [High, Finset.mem_filter] at hx
    exact hx.1
  have hXsubsetRX : X ⊆ RX := hXsub.trans (hHighSubsetU.trans hUR)
  have hYsubsetRY : Y ⊆ RY := hYsub.trans hVR
  have hunifDegAvg (A : Finset (Fin (T.S.N k))) (hA : A.Nonempty)
      (x : Fin (T.S.N k)) :
      deg (T.S.E k) c (Law.unifCore A hA).w x =
        (∑ y ∈ A, hit (T.S.E k) c x y) / A.card := by
    classical
    unfold deg
    change (∑ y, (if y ∈ A then (A.card : ℝ)⁻¹ else 0) *
      hit (T.S.E k) c x y) = _
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem_eq, ← Finset.mul_sum]
    rw [div_eq_mul_inv]
    ring
  have hscoreAvg (x : Fin (T.S.N k)) :
      score x = (∑ y ∈ V, hit (T.S.E k) c x y) / V.card := by
    simpa [score, μV] using (hunifDegAvg V hV x)
  have hrow (x : Fin (T.S.N k)) (hx : x ∈ X) :
      (1 / 2 : ℝ) + (g : ℝ) / (4 * (T.S.n k : ℝ)) ≤
        deg (T.S.E k) c (Law.unifCore Y hYne).w x := by
    let j : Fin X.card := eX ⟨x, hx⟩
    have happ := happrox j
    have hYapprox :
        |(∑ y ∈ Y, tests j y) / m - (∑ y ∈ V, tests j y) / V.card| ≤
          (T.S.n k : ℝ) ^ (-2 : ℝ) := by
      simpa [tests] using happ
    have hVavg : (∑ y ∈ V, tests j y) / V.card = score x := by
      simpa [tests, j, eX] using (hscoreAvg x).symm
    have herror : (T.S.n k : ℝ) ^ (-2 : ℝ) ≤
        (g : ℝ) / (4 * (T.S.n k : ℝ)) := by
      have hnInv : (T.S.n k : ℝ) ^ (-2 : ℝ) =
          1 / (T.S.n k : ℝ) ^ 2 := by
        rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (T.S.n k : ℝ))]
        rw [show (2 : ℝ) = (↑(2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        simp only [one_div]
      rw [hnInv]
      have hfirst : 1 / (T.S.n k : ℝ) ^ 2 ≤
          1 / (4 * (T.S.n k : ℝ)) := by
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (T.S.n k : ℝ) ^ 2)
          (by positivity : (0 : ℝ) < 4 * (T.S.n k : ℝ))).2
        have hn4 : (4 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast (by omega : 4 ≤ T.S.n k)
        have hprod := mul_nonneg (le_of_lt hnRealPos) (sub_nonneg.mpr hn4)
        nlinarith only [hprod]
      have hsecond : 1 / (4 * (T.S.n k : ℝ)) ≤
          (g : ℝ) / (4 * (T.S.n k : ℝ)) :=
        div_le_div_of_nonneg_right hGone (by positivity)
      exact hfirst.trans hsecond
    have hVlarge : (1 / 2 : ℝ) + (g : ℝ) / (2 * (T.S.n k : ℝ)) ≤ score x := by
      have hxHigh : x ∈ High := hXsub hx
      have hxHigh' : x ∈ U ∧ highThreshold ≤ score x := by simpa [High] using hxHigh
      simpa [highThreshold] using hxHigh'.2
    have hsampleLowerRow : score x - (T.S.n k : ℝ) ^ (-2 : ℝ) ≤
        (∑ y ∈ Y, tests j y) / m := by
      have hlow := (abs_le.mp hYapprox).1
      rw [hVavg] at hlow
      linarith
    have hYmean :
        (∑ y ∈ Y, tests j y) / m ≤
          deg (T.S.E k) c (Law.unifCore Y hYne).w x := by
      have hYmeanEq : (∑ y ∈ Y, tests j y) / m =
          deg (T.S.E k) c (Law.unifCore Y hYne).w x := by
        rw [← hYcard]
        simpa [tests, j, eX] using (hunifDegAvg Y hYne x).symm
      rw [hYmeanEq]
    have htarget : (1 / 2 : ℝ) + (g : ℝ) / (4 * (T.S.n k : ℝ)) ≤
        (∑ y ∈ Y, tests j y) / m := by
      have hhalf : (g : ℝ) / (4 * (T.S.n k : ℝ)) ≤
          (g : ℝ) / (2 * (T.S.n k : ℝ)) := by
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (T.S.n k : ℝ))
          (by positivity : (0 : ℝ) < 2 * (T.S.n k : ℝ))).2
        have hgn := mul_nonneg hgposReal.le hnRealPos.le
        nlinarith only [hgn]
      have hquarter : 2 * ((g : ℝ) / (4 * (T.S.n k : ℝ))) =
          (g : ℝ) / (2 * (T.S.n k : ℝ)) := by
        field_simp [ne_of_gt hnRealPos]
        norm_num
      linarith only [hVlarge, hsampleLowerRow, herror, hquarter]
    exact htarget.trans hYmean
  refine ⟨c, X, Y, hXne, hYne, hXsubsetRX, hYsubsetRY, ?_, ?_, hrow⟩
  · rw [hXcard, hYcard]
  · simpa [scale, hXcard] using hscaleM

/-- P13.3b (sections/13, lines 95–99, 148): common bins of the prescribed size,
with a diagonal codegree margin. -/
def ClusterPatchData (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) (q : ℕ) (o : Bool) (d : ℕ) : Prop :=
  ∃ (X Y : Finset (Fin (T.S.N k))) (m : ℕ)
    (B : Fin m → Finset (Fin (T.S.N k))),
    X.Nonempty ∧ Y.Nonempty ∧ 0 < d ∧ X ⊆ (if o then RY else RX) ∧
    Y ⊆ (if o then RX else RY) ∧ X.card = Y.card ∧
    (1 / 400 : ℝ) * T.S.N k * Real.exp (-(q : ℝ) ^ κ.aC) ≤ X.card ∧
    (∀ j, B j ⊆ Y) ∧ Set.PairwiseDisjoint Set.univ B ∧
    (∀ j, (B j).card = d) ∧ Y = Finset.univ.biUnion B ∧
    ∀ j y y', y ∈ B j → y' ∈ B j →
      (1 / 4 : ℝ) + 3 * κ.a ≤
        (∑ x ∈ X, hit (if o then transposeRel (T.S.E k) else T.S.E k) true x y *
          hit (if o then transposeRel (T.S.E k) else T.S.E k) true x y') / X.card

set_option maxHeartbeats 5000000 in
/-- P13.3b (sections/13, lines 148, 151–155): a cluster witness yields equal sides partitioned into bins. -/
theorem cluster_patch_from_witness (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hSampling : UniformSubsampleStatement)
    (hClean : ∀ᶠ k in atTop, ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k → RY ⊆ T.Y k → ∀ q o, IsDyadic q →
        CluScaleWitness κ T k RX RY q o → CleanClusterBins κ T k RX RY q o)
    (hBounds : ResidualScaleBoundFacts κ T) :
    ∀ᶠ k in atTop, ∀ (RX RY : Finset (Fin (T.S.N k))) (q : ℕ) (o : Bool),
      RX ⊆ T.X k → RY ⊆ T.Y k →
      IsDyadic q → κ.Q0 ≤ (q : ℝ) → CluScaleWitness κ T k RX RY q o →
      ∀ d : ℕ, 0 < d → (d : ℝ) ≤ Real.exp ((q : ℝ) / 2) →
        ClusterPatchData κ T k RX RY q o d := by
  classical
  have hgamma : (0 : ℝ) < 1 / 2 := by norm_num
  have hScaleEvent := (hBounds (1 / 2 : ℝ) hgamma).2
  have hlarge := T.S.eventually_large 1 16
  have hsampleGrowth := allocation_sample_growth T
  have hnVeryLarge := T.S.n_tendsto.eventually_ge_atTop 1000
  have hnTendsto : Tendsto (fun k : ℕ => (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
      T.S.n_tendsto
  have haPos : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hEtaTendsto := (tendsto_rpow_neg_atTop hκ.η0_pos).comp hnTendsto
  have hErrTendsto := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp hnTendsto
  have hEtaSmall : ∀ᶠ k in atTop, (T.S.n k : ℝ) ^ (-κ.η0) < κ.a :=
    hEtaTendsto.eventually (Iio_mem_nhds haPos)
  have hErrSmall : ∀ᶠ k in atTop, (T.S.n k : ℝ) ^ (-2 : ℝ) < κ.a :=
    hErrTendsto.eventually (Iio_mem_nhds haPos)
  filter_upwards [hClean, hScaleEvent, hlarge, hsampleGrowth, hnVeryLarge,
    hEtaSmall, hErrSmall] with k hcleanK hscaleK hhost hsample hnlarge hηBound hErrBound
  intro RX RY q o hRX hRY hqDyadic hqQ0 hWitness d hd hde
  have hqPos : 0 < q := by
    rcases hqDyadic with ⟨j, rfl⟩
    exact Nat.pow_pos (by omega)
  have hqTwo : 2 ≤ q := by
    by_contra hnot
    have hqOne : q = 1 := by omega
    subst q
    have hcond := hκ.Q0_large 1 (by simpa using hqQ0)
    have hsecond := hcond.2.1
    have hxiPow : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) < 1 := by
      have hp := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2)
        (by positivity : (0 : ℝ) < 10 * (κ.u : ℝ) + 100)
      change (2 : ℝ) ^ (-(10 * (κ.u : ℝ) + 100)) < 1
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      exact inv_lt_one_of_one_lt₀ hp
    have hxiLtAlpha : κ.ξ < κ.α := by
      have h := mul_lt_mul_of_pos_left hxiPow hκ.α_rng.1
      exact hκ.ξ_rng.2.trans (by simpa using h)
    have hAlphaLtOne : κ.α < 1 := by linarith [hκ.α_rng.2]
    have hxiLtOne : κ.ξ < 1 := hxiLtAlpha.trans hAlphaLtOne
    have hpow4 : (1 : ℝ) ≤ (4 : ℝ) ^ (κ.u + 3) := one_le_pow₀ (by norm_num)
    have hden : (3 : ℝ) ≤ 3 * (4 : ℝ) ^ (κ.u + 3) := by nlinarith
    have hthetaLt : κ.θ < κ.ξ ^ 2 / 3 := by
      have hfrac : κ.ξ ^ 2 / (3 * (4 : ℝ) ^ (κ.u + 3)) ≤ κ.ξ ^ 2 / 3 :=
        div_le_div_of_nonneg_left (sq_nonneg κ.ξ) (by norm_num) hden
      exact hκ.θ_rng.2.trans_le hfrac
    have hxiSq : κ.ξ ^ 2 < 1 := by
      nlinarith [sq_nonneg (1 - κ.ξ), hκ.ξ_rng.1, hxiLtOne]
    have hthetaOne : κ.θ < 1 := by nlinarith [hthetaLt, hxiSq]
    have haLtOne : κ.a < 1 := by rw [hκ.a_eq]; nlinarith [hthetaOne]
    have huPosNat : 0 < κ.u := lt_of_le_of_lt (Nat.zero_le _) hκ.u_rng.2
    have huNat : 1 ≤ κ.u := by omega
    have huReal : (1 : ℝ) ≤ (κ.u : ℝ) := by exact_mod_cast huNat
    have hpowA : Real.rpow (1 : ℝ) κ.aC = 1 := by
      simpa using (Real.one_rpow κ.aC)
    have hpowM : Real.rpow (1 : ℝ) κ.Mlo = 1 := by
      simpa using (Real.one_rpow (κ.Mlo : ℝ))
    have hsecond' : (11 : ℝ) ≤ (κ.a / 1000000) / (1000 * (κ.u : ℝ)) := by
      rw [hpowA, hpowM] at hsecond
      norm_num at hsecond
      exact hsecond
    have hdenPos : (0 : ℝ) < 1000 * (κ.u : ℝ) := by positivity
    have hnum : κ.a / 1000000 < 1 := by nlinarith
    have hrhs : (κ.a / 1000000) / (1000 * (κ.u : ℝ)) < 1 := by
      apply (div_lt_iff₀ hdenPos).2
      nlinarith [hnum, huReal]
    linarith [hsecond']
  have hqScale := hscaleK RX RY hRX hRY
  have hqScaleWitness := hqScale.1 q o hqDyadic hWitness
  have hClean := hcleanK RX RY hRX hRY q o hqDyadic hWitness
  rcases hWitness with ⟨U, hU, m₀, B, hUside, hBside, hBdisj, hBsize,
    hUcard, hBunionCard, hCorr⟩
  rcases hClean U hU m₀ B hUside hBside hBdisj hBsize hUcard hBunionCard hCorr with
    ⟨B', hB'sub, hB'disj, hB'large, hWlower, hB'degree⟩
  have hB'dSize (j : Fin m₀) (hj : (B' j).Nonempty) : d ≤ (B' j).card := by
    rcases hB'large j with hjempty | hjhalf
    · simp [hjempty] at hj
    · have hEhalf : Real.exp ((q : ℝ) / 2) ≤ Real.exp (q : ℝ) / 2 := by
        have hElarge : (2 : ℝ) ≤ Real.exp ((q : ℝ) / 2) := by
          have hqReal : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqTwo
          have hqHalf : (1 : ℝ) ≤ (q : ℝ) / 2 := by linarith
          calc
            _ ≤ Real.exp 1 := Real.exp_one_gt_two.le
            _ ≤ Real.exp ((q : ℝ) / 2) :=
              Real.exp_le_exp.mpr hqHalf
        have hsquare : Real.exp (q : ℝ) =
            Real.exp ((q : ℝ) / 2) * Real.exp ((q : ℝ) / 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hsquare]
        have hprod := mul_nonneg (Real.exp_nonneg ((q : ℝ) / 2))
          (sub_nonneg.mpr hElarge)
        nlinarith [hprod]
      have hHalfCard : Real.exp ((q : ℝ) / 2) ≤ (B' j).card := by
        calc
          _ ≤ Real.exp (q : ℝ) / 2 := hEhalf
          _ ≤ ((B j).card : ℝ) / 2 :=
            div_le_div_of_nonneg_right (hBsize j) (by norm_num : (0 : ℝ) ≤ 2)
          _ ≤ (B' j).card := by exact hjhalf
      exact_mod_cast (le_trans hde hHalfCard)
  have hB'disj' (i j : Fin m₀) (hij : i ≠ j) : Disjoint (B' i) (B' j) :=
    hB'disj (Set.mem_univ i) (Set.mem_univ j) hij
  let W : Finset (Fin (T.S.N k)) := Finset.univ.biUnion B'
  have hB'disjUniv :
      ((Finset.univ : Finset (Fin m₀)) : Set (Fin m₀)).PairwiseDisjoint B' := by
    simpa using hB'disj
  have hWcard : W.card = ∑ j : Fin m₀, (B' j).card := by
    calc
      _ = ∑ j ∈ (Finset.univ : Finset (Fin m₀)), (B' j).card :=
        Finset.card_biUnion hB'disjUniv
      _ = ∑ j : Fin m₀, (B' j).card := by simp
  let localChunks (j : Fin m₀) : Fin ((B' j).card / d) → Finset (Fin (T.S.N k)) :=
    Classical.choose (allocation_chunks_exact (B' j) d hd)
  have hlocalData (j : Fin m₀) := Classical.choose_spec
    (allocation_chunks_exact (B' j) d hd)
  have hlocalSub (j : Fin m₀) (t : Fin ((B' j).card / d)) :
      localChunks j t ⊆ B' j := (hlocalData j).1 t
  have hlocalCard (j : Fin m₀) (t : Fin ((B' j).card / d)) :
      (localChunks j t).card = d := (hlocalData j).2.1 t
  have hlocalDisj (j : Fin m₀) (t t' : Fin ((B' j).card / d)) (htt' : t ≠ t') :
      Disjoint (localChunks j t) (localChunks j t') := (hlocalData j).2.2.1 t t' htt'
  let ChunkIndex := Σ j : Fin m₀, Fin ((B' j).card / d)
  let allChunks (z : ChunkIndex) : Finset (Fin (T.S.N k)) := localChunks z.1 z.2
  have hAllSub (z : ChunkIndex) : allChunks z ⊆ W := by
    intro x hx
    apply Finset.mem_biUnion.mpr
    exact ⟨z.1, Finset.mem_univ _, hlocalSub z.1 z.2 hx⟩
  have hAllDisj (z z' : ChunkIndex) (hzz' : z ≠ z') :
      Disjoint (allChunks z) (allChunks z') := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    rcases z with ⟨i, t⟩
    rcases z' with ⟨j, t'⟩
    have hxB : x ∈ B' i := hlocalSub i t hx
    have hxB' : x ∈ B' j := hlocalSub j t' hx'
    by_cases houter : i = j
    · subst j
      have hinner : t ≠ t' := by
        intro h
        apply hzz'
        cases h
        rfl
      exact (Finset.disjoint_left.mp (hlocalDisj i t t' hinner)) hx hx'
    · exact (Finset.disjoint_left.mp (hB'disj' i j houter)) hxB hxB'
  let tAll : ℕ := Fintype.card ChunkIndex
  have hAllCard : (Finset.univ.biUnion allChunks).card = tAll * d := by
    rw [Finset.card_biUnion]
    · calc
        _ = ∑ z : ChunkIndex, (allChunks z).card := by simp
        _ = ∑ _ : ChunkIndex, d := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hlocalCard z.1 z.2
        _ = tAll * d := by simp [Finset.sum_const, tAll, nsmul_eq_mul]
    · intro z hz z' hz' hne
      exact hAllDisj z z' hne
  have hLocalHalf (j : Fin m₀) :
      (B' j).card ≤ 2 * ((B' j).card / d * d) := by
    by_cases hj : (B' j).Nonempty
    · have hdle : d ≤ (B' j).card := hB'dSize j hj
      have hquot : 1 ≤ (B' j).card / d :=
        (Nat.le_div_iff_mul_le hd).2 (by simpa using hdle)
      have hrem := Nat.mod_lt (B' j).card hd
      have hdecomp : (B' j).card % d + d * ((B' j).card / d) = (B' j).card :=
        Nat.mod_add_div _ _
      have hmul : d ≤ ((B' j).card / d) * d := by
        calc
          d = d * 1 := by simp
          _ ≤ d * ((B' j).card / d) := Nat.mul_le_mul_left d hquot
          _ = ((B' j).card / d) * d := Nat.mul_comm _ _
      have hdecomp' : (B' j).card % d + ((B' j).card / d) * d = (B' j).card := by
        simpa [Nat.mul_comm] using hdecomp
      have hrem' : (B' j).card % d < d := hrem
      omega
    · have hzero : B' j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hj
      simp [hzero]
  have hChunkCapacity : (W.card : ℝ) ≤ 2 * ((tAll * d : ℕ) : ℝ) := by
    have hsum : (∑ j : Fin m₀, (B' j).card) ≤
        2 * ∑ j : Fin m₀, ((B' j).card / d * d) := by
      calc
        _ ≤ ∑ j : Fin m₀, 2 * ((B' j).card / d * d) :=
          Finset.sum_le_sum fun j _ => hLocalHalf j
        _ = _ := by rw [Finset.mul_sum]
    have htAll : tAll = ∑ j : Fin m₀, ((B' j).card / d) := by
      simp [tAll, ChunkIndex]
    have hsumMul : ∑ j : Fin m₀, ((B' j).card / d * d) = tAll * d := by
      rw [← Finset.sum_mul, htAll]
    have hWcardR : (W.card : ℝ) = ∑ j : Fin m₀, ((B' j).card : ℝ) := by
      exact_mod_cast hWcard
    have hsumR : (∑ j : Fin m₀, ((B' j).card : ℝ)) ≤
        2 * (∑ j : Fin m₀, (((B' j).card / d * d : ℕ) : ℝ)) := by
      exact_mod_cast hsum
    have hsumMulR : (∑ j : Fin m₀, (((B' j).card / d * d : ℕ) : ℝ)) =
        ((tAll * d : ℕ) : ℝ) := by exact_mod_cast hsumMul
    calc
      _ = ∑ j : Fin m₀, ((B' j).card : ℝ) := hWcardR
      _ ≤ 2 * (∑ j : Fin m₀, (((B' j).card / d * d : ℕ) : ℝ)) := hsumR
      _ = 2 * ((tAll * d : ℕ) : ℝ) := by rw [hsumMulR]
  let L : ℝ := (T.S.N k : ℝ) * Real.exp (-(q : ℝ) ^ κ.aC)
  have hnReal : (1000 : ℝ) ≤ (T.S.n k : ℝ) := by exact_mod_cast hnlarge
  have hqReal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqSmall : (q : ℝ) < Real.sqrt (T.S.n k : ℝ) := by
    simpa [Real.sqrt_eq_rpow] using hqScaleWitness
  have hqPowerLt : Real.rpow (q : ℝ) κ.aC < (T.S.n k : ℝ) / 8 := by
    have haCLeOne : κ.aC ≤ 1 := by
      have hmin : min κ.η0 1 ≤ 1 := min_le_right _ _
      have hA : κ.aC < min κ.η0 1 / 10 ^ 6 := hκ.aC_rng.2
      nlinarith [hA, hmin]
    have hqa : Real.rpow (q : ℝ) κ.aC ≤ (q : ℝ) := by
      calc
        _ ≤ Real.rpow (q : ℝ) 1 :=
          Real.rpow_le_rpow_of_exponent_le hqReal haCLeOne
        _ = (q : ℝ) := Real.rpow_one _
    calc
      _ ≤ (q : ℝ) := hqa
      _ < Real.sqrt (T.S.n k : ℝ) := hqSmall
      _ ≤ (T.S.n k : ℝ) / 8 := by
        rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ (T.S.n k : ℝ) / 8)]
        have hn64 : (64 : ℝ) ≤ (T.S.n k : ℝ) := by linarith [hnReal]
        nlinarith [sq_nonneg ((T.S.n k : ℝ) - 64)]
  have hqPower : Real.rpow (q : ℝ) κ.aC ≤ (T.S.n k : ℝ) / 8 := hqPowerLt.le
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have htwo : Real.exp ((T.S.n k : ℝ) / 2) ≤ (2 : ℝ) ^ T.S.n k := by
    calc
      Real.exp ((T.S.n k : ℝ) / 2) ≤
          Real.exp ((T.S.n k : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr (by nlinarith [hlogTwo])
      _ = (2 : ℝ) ^ T.S.n k := by
        rw [Real.exp_nat_mul]
        simp [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hsplit : Real.exp ((T.S.n k : ℝ) / 2) *
      Real.exp (-(T.S.n k : ℝ) / 4) = Real.exp ((T.S.n k : ℝ) / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexpQuarter : Real.exp ((T.S.n k : ℝ) / 4) ≤
      (2 : ℝ) ^ T.S.n k * Real.exp (-(T.S.n k : ℝ) / 4) := by
    calc
      _ = Real.exp ((T.S.n k : ℝ) / 2) *
          Real.exp (-(T.S.n k : ℝ) / 4) := hsplit.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
  have hNlower : (2 : ℝ) ^ T.S.n k ≤ (T.S.N k : ℝ) := by
    simpa [LargeHost] using hhost.2.1
  have hLlarge : Real.exp ((T.S.n k : ℝ) / 4) ≤ L := by
    calc
      _ ≤ (2 : ℝ) ^ T.S.n k * Real.exp (-(T.S.n k : ℝ) / 4) := hexpQuarter
      _ ≤ (T.S.N k : ℝ) * Real.exp (-(T.S.n k : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hNlower (Real.exp_nonneg _)
      _ ≤ (T.S.N k : ℝ) * Real.exp (-(Real.rpow (q : ℝ) κ.aC)) := by
        have hqLE : Real.rpow (q : ℝ) κ.aC ≤ (T.S.n k : ℝ) / 4 := by
          calc
            _ ≤ (T.S.n k : ℝ) / 8 := hqPower
            _ ≤ (T.S.n k : ℝ) / 4 := by nlinarith only [hnReal]
        have harg : -(T.S.n k : ℝ) / 4 ≤ -(Real.rpow (q : ℝ) κ.aC) := by
          calc
            _ = -((T.S.n k : ℝ) / 4) := by ring
            _ ≤ _ := neg_le_neg hqLE
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr harg) (Nat.cast_nonneg _)
      _ = L := rfl
  have hdSmall : (d : ℝ) ≤ Real.exp ((T.S.n k : ℝ) / 16) := by
    calc
      _ ≤ Real.exp ((q : ℝ) / 2) := hde
      _ ≤ Real.exp (Real.sqrt (T.S.n k : ℝ) / 2) :=
        Real.exp_le_exp.mpr (by linarith [hqSmall])
      _ ≤ Real.exp ((T.S.n k : ℝ) / 16) := by
        apply Real.exp_le_exp.mpr
        have hsqrt : Real.sqrt (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) / 8 := by
          rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ (T.S.n k : ℝ) / 8)]
          nlinarith [sq_nonneg ((T.S.n k : ℝ) - 64), hnReal]
        linarith
  have hExp10 : (400 : ℝ) ≤ Real.exp 10 := by
    have hpow : (2 : ℝ) ^ 10 < Real.exp 10 := by
      calc
        _ < Real.exp 1 ^ 10 := by gcongr; exact Real.exp_one_gt_two
        _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
    have h400 : (400 : ℝ) ≤ 2 ^ 10 := by norm_num
    exact h400.trans hpow.le
  have hRatio : (400 : ℝ) * Real.exp ((T.S.n k : ℝ) / 16) ≤
      Real.exp ((T.S.n k : ℝ) / 4) := by
    have hArg : (10 : ℝ) ≤ 3 * (T.S.n k : ℝ) / 16 := by nlinarith [hnReal]
    have hExpArg : Real.exp 10 ≤ Real.exp (3 * (T.S.n k : ℝ) / 16) :=
      Real.exp_le_exp.mpr hArg
    have hsumExp : Real.exp (3 * (T.S.n k : ℝ) / 16) *
        Real.exp ((T.S.n k : ℝ) / 16) = Real.exp ((T.S.n k : ℝ) / 4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ Real.exp 10 * Real.exp ((T.S.n k : ℝ) / 16) :=
        mul_le_mul_of_nonneg_right hExp10 (Real.exp_nonneg _)
      _ ≤ Real.exp (3 * (T.S.n k : ℝ) / 16) *
          Real.exp ((T.S.n k : ℝ) / 16) :=
        mul_le_mul_of_nonneg_right hExpArg (Real.exp_nonneg _)
      _ = _ := hsumExp
  have hL400d : 400 * (d : ℝ) ≤ L := by
    calc
      _ ≤ 400 * Real.exp ((T.S.n k : ℝ) / 16) :=
        mul_le_mul_of_nonneg_left hdSmall (by norm_num)
      _ ≤ Real.exp ((T.S.n k : ℝ) / 4) := hRatio
      _ ≤ L := hLlarge
  have hWlowerL : L / 4 ≤ (W.card : ℝ) := by simpa [L, W] using hWlower
  have hChunkLower : L / 8 ≤ ((tAll * d : ℕ) : ℝ) := by
    have hcap := hChunkCapacity
    nlinarith [hWlowerL]
  have hUcardL : L ≤ (U.card : ℝ) := by simpa [L] using hUcard
  have h400dNat : 400 * d ≤ U.card := by
    exact_mod_cast (le_trans hL400d hUcardL)
  have hdleU : d ≤ U.card := by omega
  have hUdivLower : U.card - d ≤ U.card / d * d := by
    have hrem := Nat.mod_lt U.card hd
    have hdecomp : U.card % d + (U.card / d) * d = U.card := by
      simpa [Nat.mul_comm] using (Nat.mod_add_div U.card d)
    omega
  have hUsubCast : ((U.card - d : ℕ) : ℝ) = (U.card : ℝ) - (d : ℝ) := by
    rw [Nat.cast_sub hdleU]
  have hdL : (d : ℝ) ≤ L / 400 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 400)).2
    simpa [mul_comm] using hL400d
  have hUsubL : L / 8 ≤ ((U.card - d : ℕ) : ℝ) := by
    rw [hUsubCast]
    nlinarith [hUcardL, hdL]
  have hUdivCapacity : L / 8 ≤ ((U.card / d * d : ℕ) : ℝ) := by
    exact hUsubL.trans (by exact_mod_cast hUdivLower)
  let tSel : ℕ := min tAll (U.card / d)
  let M : ℕ := tSel * d
  have hMmul : M = min (tAll * d) (U.card / d * d) := by
    dsimp [M, tSel]
    by_cases h : tAll ≤ U.card / d
    · rw [min_eq_left h, min_eq_left (Nat.mul_le_mul_right d h)]
    · have h' : U.card / d ≤ tAll := by omega
      rw [min_eq_right h', min_eq_right (Nat.mul_le_mul_right d h')]
  have hMlower : L / 8 ≤ (M : ℝ) := by
    rw [hMmul, Nat.cast_min]
    exact le_min hChunkLower hUdivCapacity
  have hLpoly : (16 : ℝ) * (T.S.n k : ℝ) ^ 12 ≤ L := by
    calc
      _ ≤ (2 : ℝ) ^ T.S.n k * Real.exp (-(T.S.n k : ℝ) / 4) := hsample
      _ ≤ (T.S.N k : ℝ) * Real.exp (-(T.S.n k : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hNlower (Real.exp_nonneg _)
      _ ≤ L := by
        calc
          _ ≤ (T.S.N k : ℝ) * Real.exp (-(Real.rpow (q : ℝ) κ.aC)) := by
            have hqLE : Real.rpow (q : ℝ) κ.aC ≤ (T.S.n k : ℝ) / 4 :=
              le_trans hqPower (by nlinarith only [hnReal])
            have harg : -(T.S.n k : ℝ) / 4 ≤ -(Real.rpow (q : ℝ) κ.aC) := by
              calc
                _ = -((T.S.n k : ℝ) / 4) := by ring
                _ ≤ _ := neg_le_neg hqLE
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr harg) (Nat.cast_nonneg _)
          _ = L := rfl
  have hMSmall : (T.S.n k) ^ 12 ≤ M := by
    have hn12 : (T.S.n k : ℝ) ^ 12 ≤ L / 16 := by nlinarith [hLpoly]
    have hMvs : L / 16 ≤ (M : ℝ) := by nlinarith [hMlower]
    exact_mod_cast (hn12.trans hMvs)
  have hMpos : 0 < M := by
    have hn12 : 0 < (T.S.n k) ^ 12 := Nat.pow_pos (by omega)
    omega
  have hMleU : M ≤ U.card := by
    dsimp [M]
    calc
      _ ≤ (U.card / d) * d := Nat.mul_le_mul_right d (Nat.min_le_right _ _)
      _ ≤ U.card := Nat.div_mul_le_self _ _
  have htsel : tSel ≤ (Finset.univ : Finset ChunkIndex).card := by
    dsimp [tSel, tAll]
    exact Nat.min_le_left _ _
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq htsel
  let eJ : {z : ChunkIndex // z ∈ J} ≃ Fin tSel :=
    Fintype.equivFinOfCardEq (by simp [hJcard])
  let outBins : Fin tSel → Finset (Fin (T.S.N k)) :=
    fun i => allChunks (eJ.symm i).val
  have hOutCard (i : Fin tSel) : (outBins i).card = d := by
    let z : ChunkIndex := (eJ.symm i).val
    exact hlocalCard z.1 z.2
  have hOutDisj (i j : Fin tSel) (hij : i ≠ j) : Disjoint (outBins i) (outBins j) := by
    apply hAllDisj
    intro heq
    apply hij
    apply eJ.symm.injective
    exact Subtype.ext heq
  let Y : Finset (Fin (T.S.N k)) := Finset.univ.biUnion outBins
  have hYcard : Y.card = M := by
    have h := Finset.card_biUnion (s := (Finset.univ : Finset (Fin tSel)))
      (t := outBins) (by
        intro i hi j hj hij
        exact hOutDisj i j hij)
    dsimp [Y, M, tSel] at h ⊢
    rw [h]
    simp_rw [hOutCard]
    simp
  have hYsubSide : Y ⊆ (if o then RX else RY) := by
    intro y hy
    rcases Finset.mem_biUnion.mp hy with ⟨i, hi, hyi⟩
    let z := (eJ.symm i).val
    have hy' : y ∈ B' z.1 := hlocalSub z.1 z.2 hyi
    exact hBside z.1 (hB'sub z.1 hy')
  have hYcardN : Y.card ≤ T.S.N k := by simpa using (Finset.card_le_univ Y)
  let Eo : Fin (T.S.N k) → Fin (T.S.N k) → Prop :=
    if o then transposeRel (T.S.E k) else T.S.E k
  let eY : {y : Fin (T.S.N k) // y ∈ Y} ≃ Fin Y.card :=
    Fintype.equivFinOfCardEq (by simp)
  let ePair : (Fin Y.card × Fin Y.card) ≃ Fin (Y.card ^ 2) :=
    Fintype.equivFinOfCardEq (by simp [pow_two])
  let tests : Fin (Y.card ^ 2) → Fin (T.S.N k) → ℝ := fun j x =>
    let p := ePair.symm j
    hit Eo true x (eY.symm p.1).val * hit Eo true x (eY.symm p.2).val
  have hHitRange (x y : Fin (T.S.N k)) :
      0 ≤ hit Eo true x y ∧ hit Eo true x y ≤ 1 := by
    unfold hit
    split_ifs <;> norm_num
  have htests (j : Fin (Y.card ^ 2)) (x : Fin (T.S.N k)) :
      0 ≤ tests j x ∧ tests j x ≤ 1 := by
    dsimp [tests]
    let p := ePair.symm j
    rcases hHitRange x (eY.symm p.1).val with ⟨ha0, ha1⟩
    rcases hHitRange x (eY.symm p.2).val with ⟨hb0, hb1⟩
    constructor
    · exact mul_nonneg ha0 hb0
    · calc
        _ ≤ 1 * hit Eo true x (eY.symm p.2).val :=
          mul_le_mul_of_nonneg_right ha1 hb0
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb1 (by norm_num)
        _ = 1 := by ring
  have hExp2 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := by gcongr; exact Real.exp_one_gt_two.le
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h4Ceil : (4 : ℕ) ^ T.S.n k ≤
      Nat.ceil (Real.exp (2 * (T.S.n k : ℝ))) := by
    have h4Exp : (4 : ℝ) ^ T.S.n k ≤ Real.exp (2 * (T.S.n k : ℝ)) := by
      calc
        _ ≤ Real.exp 2 ^ T.S.n k := by gcongr
        _ = Real.exp (2 * (T.S.n k : ℝ)) := by
          rw [show 2 * (T.S.n k : ℝ) = (T.S.n k : ℝ) * 2 by ring,
            Real.exp_nat_mul]
    have hceil : (4 : ℝ) ^ T.S.n k ≤
        (Nat.ceil (Real.exp (2 * (T.S.n k : ℝ))) : ℝ) :=
      h4Exp.trans (Nat.le_ceil _)
    exact_mod_cast hceil
  have hnPow2 : (T.S.n k) ^ 2 ≤ (T.S.n k) ^ 4 := by
    calc
      _ = (T.S.n k) ^ 2 * 1 := by simp
      _ ≤ (T.S.n k) ^ 2 * (T.S.n k) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.one_le_pow 2 _ (by omega))
      _ = (T.S.n k) ^ 4 := by ring
  have hJbound : Y.card ^ 2 ≤
      Nat.ceil (Real.exp (2 * (T.S.n k : ℝ))) * (T.S.n k) ^ 4 := by
    calc
      _ ≤ (T.S.N k) ^ 2 := Nat.pow_le_pow_left hYcardN _
      _ ≤ (T.S.n k * 2 ^ T.S.n k) ^ 2 := Nat.pow_le_pow_left hhost.2.2 _
      _ = (T.S.n k) ^ 2 * (4 : ℕ) ^ T.S.n k := by
        calc
          _ = (T.S.n k) ^ 2 * ((2 : ℕ) ^ T.S.n k * 2 ^ T.S.n k) := by ring
          _ = (T.S.n k) ^ 2 * (4 : ℕ) ^ T.S.n k := by
            congr 1
            rw [← Nat.mul_pow]
      _ ≤ (T.S.n k) ^ 2 * Nat.ceil (Real.exp (2 * (T.S.n k : ℝ))) :=
        Nat.mul_le_mul_left _ h4Ceil
      _ ≤ (T.S.n k) ^ 4 * Nat.ceil (Real.exp (2 * (T.S.n k : ℝ))) :=
        Nat.mul_le_mul_right _ hnPow2
      _ = _ := Nat.mul_comm _ _
  obtain ⟨X, hXsub, hXcard, hApprox⟩ :=
    hSampling (T.S.N k) (Y.card ^ 2) M (T.S.n k) U tests (by omega)
      hMleU hMSmall hJbound htests
  have hXne : X.Nonempty := Finset.card_pos.mp (by rw [hXcard]; exact hMpos)
  have hXsubSide : X ⊆ (if o then RY else RX) := hXsub.trans hUside
  let μU := Law.unifCore U hU
  let avgU : Fin (T.S.N k) → Fin (T.S.N k) → ℝ := fun y y' =>
    (∑ x ∈ U, hit Eo true x y * hit Eo true x y') / U.card
  let avgX : Fin (T.S.N k) → Fin (T.S.N k) → ℝ := fun y y' =>
    (∑ x ∈ X, hit Eo true x y * hit Eo true x y') / M
  have hUniformAvg (y y' : Fin (T.S.N k)) :
      avgU y y' = ∑ x, μU.w x * hit Eo true x y * hit Eo true x y' := by
    simpa [avgU, μU, mul_assoc] using
      (allocation_unifCore_sum U hU (fun x => hit Eo true x y * hit Eo true x y')).symm
  have hMeanIdentity (y y' : Fin (T.S.N k)) :
      avgU y y' =
        (1 + (2 * colDeg Eo true μU y - 1) +
          (2 * colDeg Eo true μU y' - 1) + pairCorr Eo false μU y y') / 4 := by
    calc
      _ = ∑ x, μU.w x * hit Eo true x y * hit Eo true x y' := hUniformAvg y y'
      _ = _ := by
        simpa [Eo, mul_assoc] using
          (codegree_identity (T.S.N k) Eo true μU y y')
  have hdegClose (j : Fin m₀) (y : Fin (T.S.N k)) (hy : y ∈ B' j) :
      |colDeg Eo true μU y - 1 / 2| ≤ (T.S.n k : ℝ) ^ (-κ.η0) := by
    have h := hB'degree j y hy
    cases o with
    | false => simpa [Eo] using h
    | true =>
        simpa [Eo, colDeg, rowDeg, transposeRel, hit, Hits] using h
  have hpairCorr (j : Fin m₀) (y y' : Fin (T.S.N k))
      (hy : y ∈ B' j) (hy' : y' ∈ B' j) (hne : y ≠ y') :
      κ.θ < pairCorr Eo false μU y y' := by
    have h := hCorr j y (hB'sub j hy) y' (hB'sub j hy') hne
    cases o <;> simpa [Eo, pairCorr_transpose] using h
  have hHitSq (x y : Fin (T.S.N k)) :
      hit Eo true x y * hit Eo true x y = hit Eo true x y := by
    unfold hit
    split_ifs <;> norm_num
  have hxiPow : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) < 1 := by
    have hp := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < 10 * (κ.u : ℝ) + 100)
    change (2 : ℝ) ^ (-(10 * (κ.u : ℝ) + 100)) < 1
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ hp
  have hxiLtAlpha : κ.ξ < κ.α := by
    have h := mul_lt_mul_of_pos_left hxiPow hκ.α_rng.1
    exact hκ.ξ_rng.2.trans (by simpa using h)
  have hxiLtOne : κ.ξ < 1 := hxiLtAlpha.trans (by linarith [hκ.α_rng.2])
  have hpow4 : (1 : ℝ) ≤ (4 : ℝ) ^ (κ.u + 3) := one_le_pow₀ (by norm_num)
  have hden4 : (3 : ℝ) ≤ 3 * (4 : ℝ) ^ (κ.u + 3) := by nlinarith
  have hthetaLt : κ.θ < κ.ξ ^ 2 / 3 := by
    have hfrac : κ.ξ ^ 2 / (3 * (4 : ℝ) ^ (κ.u + 3)) ≤ κ.ξ ^ 2 / 3 :=
      div_le_div_of_nonneg_left (sq_nonneg κ.ξ) (by norm_num) hden4
    exact hκ.θ_rng.2.trans_le hfrac
  have hthetaOne : κ.θ < 1 := by
    have hxiSq : κ.ξ ^ 2 < 1 := by
      nlinarith [sq_nonneg (1 - κ.ξ), hκ.ξ_rng.1, hxiLtOne]
    nlinarith [hthetaLt, hxiSq]
  have haSmall : κ.a < 1 / 8 := by rw [hκ.a_eq]; nlinarith [hthetaOne]
  have hthetaEq : κ.θ = 100 * κ.a := by rw [hκ.a_eq]; field_simp
  have hdegLower (j : Fin m₀) (y : Fin (T.S.N k)) (hy : y ∈ B' j) :
      1 / 2 - κ.a ≤ colDeg Eo true μU y := by
    have h := (abs_le.mp (hdegClose j y hy)).1
    linarith [hηBound]
  have hMeanLower (j : Fin m₀) (y y' : Fin (T.S.N k))
      (hy : y ∈ B' j) (hy' : y' ∈ B' j) :
      1 / 4 + 4 * κ.a ≤ avgU y y' := by
    by_cases hEq : y = y'
    · subst y'
      have hdeg := hdegLower j y hy
      have havg : avgU y y = colDeg Eo true μU y := by
        calc
          _ = ∑ x, μU.w x * hit Eo true x y * hit Eo true x y := hUniformAvg y y
          _ = ∑ x, μU.w x * hit Eo true x y := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [mul_assoc, hHitSq]
          _ = colDeg Eo true μU y := by
            symm
            simp [colDeg, hit, Hits]
      rw [havg]
      nlinarith [hdeg, haSmall]
    · have hcorr := hpairCorr j y y' hy hy' hEq
      have hdeg1 := hdegLower j y hy
      have hdeg2 := hdegLower j y' hy'
      rw [hMeanIdentity]
      nlinarith [hcorr, hdeg1, hdeg2, hthetaEq]
  have hApproxPair (y y' : Fin (T.S.N k)) (hy : y ∈ Y) (hy' : y' ∈ Y) :
      |avgX y y' - avgU y y'| ≤ (T.S.n k : ℝ) ^ (-2 : ℝ) := by
    let p : Fin Y.card × Fin Y.card := (eY ⟨y, hy⟩, eY ⟨y', hy'⟩)
    have h := hApprox (ePair p)
    simpa [tests, avgX, avgU, p] using h
  have hAvgXLower (j : Fin m₀) (y y' : Fin (T.S.N k))
      (hyB : y ∈ B' j) (hyB' : y' ∈ B' j) (hy : y ∈ Y) (hy' : y' ∈ Y) :
      1 / 4 + 3 * κ.a ≤ avgX y y' := by
    have happrox := (abs_le.mp (hApproxPair y y' hy hy')).1
    have hmean := hMeanLower j y y' hyB hyB'
    linarith [happrox, hmean, hErrBound]
  have hOutSubY (i : Fin tSel) : outBins i ⊆ Y := by
    intro y hy
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hy⟩
  have hYne : Y.Nonempty := Finset.card_pos.mp (by rw [hYcard]; exact hMpos)
  have hOutSetDisj : Set.PairwiseDisjoint Set.univ outBins := by
    intro i hi j hj hij
    exact hOutDisj i j hij
  have hCodegree (i : Fin tSel) (y y' : Fin (T.S.N k))
      (hy : y ∈ outBins i) (hy' : y' ∈ outBins i) :
      (1 / 4 : ℝ) + 3 * κ.a ≤
        (∑ x ∈ X, hit Eo true x y * hit Eo true x y') / X.card := by
    let z : ChunkIndex := (eJ.symm i).val
    have hyB : y ∈ B' z.1 := hlocalSub z.1 z.2 hy
    have hyB' : y' ∈ B' z.1 := hlocalSub z.1 z.2 hy'
    have hyY : y ∈ Y := hOutSubY i hy
    have hyY' : y' ∈ Y := hOutSubY i hy'
    have hlower := hAvgXLower z.1 y y' hyB hyB' hyY hyY'
    change (1 / 4 : ℝ) + 3 * κ.a ≤
      (∑ x ∈ X, hit Eo true x y * hit Eo true x y') / M at hlower
    rw [← hXcard] at hlower
    simpa [Eo] using hlower
  have hScaleFinal :
      (1 / 400 : ℝ) * (T.S.N k : ℝ) * Real.exp (-(q : ℝ) ^ κ.aC) ≤ (X.card : ℝ) := by
    rw [hXcard]
    dsimp [L] at hMlower ⊢
    nlinarith [hMlower]
  refine ⟨X, Y, tSel, outBins, hXne, hYne, hd, hXsubSide, hYsubSide,
    ?_, hScaleFinal, hOutSubY, hOutSetDisj, hOutCard, ?_, hCodegree⟩
  · rw [hXcard, hYcard]
  · rfl

/-- P13.3c (sections/13, line 140): truncate two large residual sides to a common size. -/
theorem bounded_patch (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k)))
    (hX : (T.S.N k : ℝ) / 2 ≤ RX.card) (hY : (T.S.N k : ℝ) / 2 ≤ RY.card) :
    ∃ X Y : Finset (Fin (T.S.N k)), X.Nonempty ∧ Y.Nonempty ∧
      X ⊆ RX ∧ Y ⊆ RY ∧ X.card = Y.card ∧
      (1 / 400 : ℝ) * T.S.N k ≤ X.card := by
  classical
  let m := min RX.card RY.card
  obtain ⟨X, hXsub, hXcard⟩ := Finset.exists_subset_card_eq (Nat.min_le_left _ _)
  obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_subset_card_eq (Nat.min_le_right _ _)
  have hNpos : 0 < (T.S.N k : ℝ) := by
    exact_mod_cast T.S.N_pos k
  have hmin : (T.S.N k : ℝ) / 2 ≤ (m : ℝ) := by
    dsimp [m]
    rw [Nat.cast_min]
    exact le_min hX hY
  have hmpos : 0 < m := by
    exact_mod_cast (show (0 : ℝ) < (m : ℝ) by linarith)
  have hXne : X.Nonempty := Finset.card_pos.mp (by rw [hXcard]; exact hmpos)
  have hYne : Y.Nonempty := Finset.card_pos.mp (by rw [hYcard]; exact hmpos)
  refine ⟨X, Y, hXne, hYne, hXsub, hYsub, ?_, ?_⟩
  · rw [hXcard, hYcard]
  · rw [hXcard]
    linarith

/-- D13.T/P13.3d (sections/13, lines 52–126, 128–159): extraction data independent of prefix allocation. -/
/- The extraction data which does not depend on the prefix words or on the
allocation estimates. This is the output of the repeated patch passes. -/
structure ExtractionData {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) : Prop where
  reserveX_card : 𝒯.reserveX.card = T.S.N k / 3
  reserveY_card : 𝒯.reserveY.card = T.S.N k / 3
  reserveX_subset : 𝒯.reserveX ⊆ T.X k
  reserveY_subset : 𝒯.reserveY ⊆ T.Y k
  patch_supports : ∀ i, (𝒯.P i).X ⊆ (𝒯.P i).resX ∧
    (𝒯.P i).resX ⊆ T.X k \ 𝒯.reserveX ∧
    (𝒯.P i).Y ⊆ (𝒯.P i).resY ∧
    (𝒯.P i).resY ⊆ T.Y k \ 𝒯.reserveY
  patch_nonempty : ∀ i, (𝒯.P i).X.Nonempty ∧ (𝒯.P i).Y.Nonempty
  bins_card : ∀ i, ∀ B ∈ (𝒯.P i).bins.parts, B.card = (𝒯.P i).d
  patch_X_disjoint : ∀ i j, i ≠ j → Disjoint (𝒯.P i).X (𝒯.P j).X
  patch_Y_disjoint : ∀ i j, i ≠ j → Disjoint (𝒯.P i).Y (𝒯.P j).Y
  S_upper : 𝒯.S ≤ T.S.N k
  measured_scales : ∀ i, (𝒯.P i).g = gScale κ T k (𝒯.P i).resX (𝒯.P i).resY ∧
    (𝒯.P i).q = qScale κ T k (𝒯.P i).resX (𝒯.P i).resY
  bounded_scale_cutoff : 𝒯.mode = .bounded → ∀ i,
    max (𝒯.P i).g (𝒯.P i).q < κ.M1 * κ.Q0
  bounded_data : 𝒯.mode = .bounded → 𝒯.m = 1 ∧ ∀ i,
    (𝒯.P i).ℓ = 0 ∧ (𝒯.P i).h = 0 ∧ (𝒯.P i).d = 1 ∧
    (1 / 400 : ℝ) * T.S.N k ≤ (𝒯.P i).M ∧ 𝒯.Q i = κ.Qbd
  /-- The eventual residual-scale bound for direct modes, required by `Tiling.Valid` (consumed in Section 15). -/
  direct_scale_bound : (𝒯.mode = .lowDirect ∨ 𝒯.mode = .highDirect) → ∀ i,
    ((𝒯.P i).g : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.ι / 2)
  direct_data : (𝒯.mode = .lowDirect ∨ 𝒯.mode = .highDirect) → ∀ i,
    κ.M1 * κ.Q0 ≤ max (𝒯.P i).g (𝒯.P i).q ∧
    κ.M1 * (𝒯.P i).q < (𝒯.P i).g ∧
    (1 / 400 : ℝ) * T.S.N k * Real.exp (-Real.rpow ((𝒯.P i).g : ℝ) κ.aB) ≤ (𝒯.P i).M ∧
    (∀ x ∈ (𝒯.P i).X,
      (1 / 2 : ℝ) + (𝒯.P i).g / (4 * T.S.n k) ≤
        deg (T.S.E k) 𝒯.c (Law.unifCore (𝒯.P i).Y (patch_nonempty i).2).w x) ∧
    (𝒯.P i).h = 0 ∧ (𝒯.P i).d = 1 ∧
    ((𝒯.mode = .highDirect) ↔ κ.KB * Real.log (T.S.n k) < (𝒯.P i).g)
  cluster_data : (𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨ 𝒯.mode = .highLarge) → ∀ i,
    κ.M1 * κ.Q0 ≤ max (𝒯.P i).g (𝒯.P i).q ∧
    (𝒯.P i).g ≤ κ.M1 * (𝒯.P i).q ∧
    (1 / 400 : ℝ) * T.S.N k * Real.exp (-Real.rpow ((𝒯.P i).q : ℝ) κ.aC) ≤ (𝒯.P i).M ∧
    ((𝒯.mode = .highSmall) →
      (𝒯.P i).d = min ⌊Real.exp ((𝒯.P i).q / 2)⌋₊
        ⌊Real.exp (Real.sqrt (Real.log (T.S.n k)))⌋₊) ∧
    ((𝒯.mode = .lowCluster ∨ 𝒯.mode = .highLarge) →
      (𝒯.P i).d = ⌊Real.exp ((𝒯.P i).q / 2)⌋₊) ∧
    (∀ B ∈ (𝒯.P i).bins.parts, ∀ y ∈ B, ∀ y' ∈ B,
      (1 / 4 : ℝ) + 3 * κ.a ≤
        (∑ x ∈ (𝒯.P i).X,
          hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y') / (𝒯.P i).M) ∧
    (𝒯.P i).h = 2 ^ Nat.log2 (𝒯.P i).h ∧
    (Real.rpow (𝒯.P i).q (if 𝒯.mode = .lowCluster then κ.Mlo else κ.Mhi) ≤ (𝒯.P i).h) ∧
    ((𝒯.P i).h : ℝ) < 2 * Real.rpow (𝒯.P i).q
      (if 𝒯.mode = .lowCluster then κ.Mlo else κ.Mhi) ∧
    ((𝒯.mode = .lowCluster) ↔
      (𝒯.P i).q ≤ Real.rpow (Real.log (T.S.n k)) κ.cq) ∧
    ((𝒯.mode = .highSmall) ↔
      (Real.rpow (Real.log (T.S.n k)) κ.cq < (𝒯.P i).q ∧
       (𝒯.P i).q ≤ (Real.log (T.S.n k)) ^ 2)) ∧
    ((𝒯.mode = .highLarge) ↔ (Real.log (T.S.n k)) ^ 2 < (𝒯.P i).q)
  clique_scales : ∀ i,
    (𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨ 𝒯.mode = .highLarge →
      IsDyadic (𝒯.Q i) ∧ (𝒯.P i).q ^ 2 ≤ 𝒯.Q i ∧
      (𝒯.Q i : ℝ) ≤ 2 * (𝒯.P i).q ^ 2 ∧ 𝒯.kScale i < 𝒯.Q i) ∧
    ((𝒯.mode = .lowDirect ∨ 𝒯.mode = .highDirect) →
      IsDyadic (𝒯.Q i) ∧ (𝒯.P i).g / (2 * Real.sqrt κ.M1) < 𝒯.Q i ∧
      (𝒯.Q i : ℝ) ≤ 2 * (𝒯.P i).g / Real.sqrt κ.M1 ∧ (𝒯.P i).q < 𝒯.Q i)

/-- Changing only the prefix words preserves every extraction fact. -/
private theorem extractionData_withWords {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (h𝒯 : ExtractionData 𝒯)
    (w : Fin 𝒯.m → CubePos (T.S.n k)) :
    ExtractionData (κ := κ) (T := T) (k := k) {𝒯 with w := w} := by
  cases 𝒯 with
  | mk mode c m P S oldWords reserveX reserveY Q =>
    cases h𝒯
    constructor <;> assumption

/-- P13.3d–e (sections/13, lines 128–168): one uniform mode/orientation/colour family. -/
structure PassFamily (κ : CConsts) (T : Stage) (k : ℕ) where
  orientation : Bool
  tiling : Tiling κ (T.orient orientation) k
  extracted : ExtractionData tiling
  mass_sum : ∑ i, (tiling.P i).M = tiling.S

/-- P13.3d (sections/13, lines 128–159): extraction pass families grouped by finite type. -/
structure PassCollection (κ : CConsts) (T : Stage) (k : ℕ) where
  families : List (PassFamily κ T k)
  families_mass : ∀ f ∈ families, ∑ i, (f.tiling.P i).M = f.tiling.S
  type_tags_nodup : (families.map fun f : PassFamily κ T k =>
    (f.orientation, f.tiling.mode, f.tiling.c)).Nodup
  mass_or_bounded :
    (∃ f ∈ families, f.tiling.mode = .bounded ∧
      (1 / 400 : ℝ) * T.S.N k ≤ f.tiling.S) ∨
    ((families.filter fun f => f.tiling.mode ≠ .bounded).map
      (fun f => f.tiling.S)).sum * 10 ≥ T.S.N k

/-- P13.3f (sections/13, lines 170–182): rounded family with dyadic weights summing to one. -/
structure RoundedFamily (κ : CConsts) (T : Stage) (k : ℕ) where
  orientation : Bool
  tiling : Tiling κ (T.orient orientation) k
  extracted : ExtractionData tiling
  S_lower : (1 / 400 : ℝ) * T.S.N k ≤ tiling.S
  S_upper : tiling.S ≤ T.S.N k
  selected_mass : (tiling.S : ℝ) / 2 < ∑ i, (tiling.P i).M
  dyadic_mass_lower : ∀ i, (tiling.P i).M / tiling.S ≤
    (2 : ℝ) ^ (-((tiling.P i).ℓ : ℤ))
  dyadic_mass_upper : ∀ i,
    (2 : ℝ) ^ (-((tiling.P i).ℓ : ℤ)) < 2 * (tiling.P i).M / tiling.S
  dyadic_sum : ∑ i, (2 : ℝ) ^ (-((tiling.P i).ℓ : ℤ)) = 1

/-- P13.3f (sections/13, lines 170–182): rounding retains an injective
subfamily, keeps the pre-restriction mass and reserves, and changes only
prefix lengths. `HEq` transports patches across the equal orientations. -/
structure RoundingProvenance {κ : CConsts} {T : Stage} {k : ℕ}
    (f : PassFamily κ T k) (R : RoundedFamily κ T k) where
  orientation : R.orientation = f.orientation
  mode : R.tiling.mode = f.tiling.mode
  colour : R.tiling.c = f.tiling.c
  mass : R.tiling.S = f.tiling.S
  reserveX : HEq R.tiling.reserveX f.tiling.reserveX
  reserveY : HEq R.tiling.reserveY f.tiling.reserveY
  index : Fin R.tiling.m → Fin f.tiling.m
  injective : Function.Injective index
  patches : ∀ i, HEq
    {R.tiling.P i with ℓ := (f.tiling.P (index i)).ℓ} (f.tiling.P (index i))
  clique_scales : ∀ i, R.tiling.Q i = f.tiling.Q (index i)

/-- P13.3h (sections/13, lines 193, 210): all prefixes leave a free coordinate,
and all internal tails lie beyond every prefix. -/
structure PrefixDimensionFit {κ : CConsts} {T : Stage} {k : ℕ}
    (R : RoundedFamily κ T k) : Prop where
  free : ∀ i, (R.tiling.P i).ℓ < (T.orient R.orientation).S.n k
  fit : (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).ℓ) +
    (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).h) ≤
      (T.orient R.orientation).S.n k

/-- P13.3g (sections/13, lines 170–182): complete prefix-code property for assigned words. -/
def PrefixCodeComplete {κ : CConsts} {T : Stage} {k : ℕ}
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k)) : Prop :=
  ∀ v : CubePos ((T.orient R.orientation).S.n k), ∃! i,
    v ∈ prefixLeaf (R.tiling.P i).ℓ (w i)

/-- P13.3h (sections/13, lines 184–204): parity counts, crossing flips, and internal-coordinate fit. -/
structure PrefixGeometry {κ : CConsts} {T : Stage} {k : ℕ}
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k)) : Prop where
  prefix_internal_length :
    (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).ℓ) +
      (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).h) ≤
        (T.orient R.orientation).S.n k
  leaf_card : ∀ i, Fintype.card {v : CubePos ((T.orient R.orientation).S.n k) //
      v ∈ prefixLeaf (R.tiling.P i).ℓ (w i)} =
        2 ^ ((T.orient R.orientation).S.n k - (R.tiling.P i).ℓ)
  parity_leaf_card : ∀ i,
    Fintype.card {v : CubePos ((T.orient R.orientation).S.n k) //
      v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) ∧ IsEvenRole v} =
        2 ^ ((T.orient R.orientation).S.n k - (R.tiling.P i).ℓ - 1)
  odd_leaf_card : ∀ i,
    Fintype.card {v : CubePos ((T.orient R.orientation).S.n k) //
      v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) ∧ ¬ IsEvenRole v} =
        2 ^ ((T.orient R.orientation).S.n k - (R.tiling.P i).ℓ - 1)
  role_count_bounds : ∀ i,
    (2 : ℝ) ^ ((T.orient R.orientation).S.n k - 1) *
        (R.tiling.P i).M / (T.S.N k : ℝ) ≤
          (Fintype.card {v : CubePos ((T.orient R.orientation).S.n k) //
            v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) ∧ IsEvenRole v} : ℝ) ∧
      (Fintype.card {v : CubePos ((T.orient R.orientation).S.n k) //
          v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) ∧ IsEvenRole v} : ℝ) ≤
        (2 : ℝ) ^ ((T.orient R.orientation).S.n k) *
          (R.tiling.P i).M / ((1 / 400 : ℝ) * T.S.N k)
  crossing_flips : ∀ i (v : CubePos ((T.orient R.orientation).S.n k)),
    v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) →
    ∃ f : {j : Fin ((T.orient R.orientation).S.n k) //
      j.val < (R.tiling.P i).ℓ} → Fin R.tiling.m,
      (∀ j, f j ≠ i ∧
        Function.update v j.1 (!v j.1) ∈
          prefixLeaf (R.tiling.P (f j)).ℓ (w (f j))) ∧ Function.Injective f
  coordinate_partition : ∀ i,
    Tiling.crossingCoords R.tiling i ∪
      (Tiling.bulkCoords R.tiling i ∪ Tiling.Icoord R.tiling i) = Finset.univ
  coordinate_disjoint : ∀ i,
    Disjoint (Tiling.crossingCoords R.tiling i) (Tiling.bulkCoords R.tiling i) ∧
    Disjoint (Tiling.crossingCoords R.tiling i) (Tiling.Icoord R.tiling i) ∧
    Disjoint (Tiling.bulkCoords R.tiling i) (Tiling.Icoord R.tiling i)
  internal_card : ∀ i, (Tiling.Icoord R.tiling i).card = (R.tiling.P i).h
  internal_nested : ∀ i j, (R.tiling.P i).h ≤ (R.tiling.P j).h →
    Tiling.Icoord R.tiling i ⊆ Tiling.Icoord R.tiling j

/-- Attach the Kraft words to the extracted family. -/
private def withPrefixWords {κ : CConsts} {T : Stage} {k : ℕ}
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k)) :
    RoundedFamily κ T k where
  orientation := R.orientation
  tiling := {R.tiling with w := w}
  extracted := extractionData_withWords R.extracted w
  S_lower := R.S_lower
  S_upper := R.S_upper
  selected_mass := R.selected_mass
  dyadic_mass_lower := R.dyadic_mass_lower
  dyadic_mass_upper := R.dyadic_mass_upper
  dyadic_sum := R.dyadic_sum

/-- Attaching words preserves the retained subfamily and all extraction data. -/
private def roundingProvenance_withWords {κ : CConsts} {T : Stage} {k : ℕ}
    {f : PassFamily κ T k} {R : RoundedFamily κ T k}
    (h : RoundingProvenance f R)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k)) :
    RoundingProvenance f (withPrefixWords R w) where
  orientation := h.orientation
  mode := h.mode
  colour := h.colour
  mass := h.mass
  reserveX := h.reserveX
  reserveY := h.reserveY
  index := h.index
  injective := h.injective
  patches := h.patches
  clique_scales := h.clique_scales

/-- P13.3i (sections/13, lines 151–155, 205–215): scale and gain inequalities required by later sections. -/
def AllocationBounds {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) : Prop :=
  ∀ i, (max (𝒯.P i).h (𝒯.P i).ℓ : ℝ) < (T.S.n k : ℝ) ^ κ.ι ∧
    (𝒯.mode = .bounded ∨
      ((𝒯.P i).ℓ : ℝ) ≤ 𝒯.gain i / (1000 * κ.u) ∧
      Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) ≤ 𝒯.gain i / (1000 * κ.u))

/-- P13.3i (sections/13, lines 151–155, 205–215): estimates selecting later low and high modes. -/
def ScaleRegimeFacts {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) : Prop :=
  (∀ i, 𝒯.mode.isCluster →
    (𝒯.kScale i : ℝ) * 𝒯.tScale i ≤ Real.rpow ((𝒯.P i).q : ℝ) (κ.aC / 2) ∧
      (𝒯.kScale i : ℝ) * 𝒯.tScale i < Real.log (𝒯.P i).d) ∧
  (𝒯.mode = .lowCluster → ∀ i,
    ((𝒯.P i).h : ℝ) ≤ Real.rpow (Real.log (T.S.n k)) (1 / 10 : ℝ)) ∧
  ((𝒯.mode = .highSmall ∨ 𝒯.mode = .highLarge) → ∀ i,
    (Real.log (T.S.n k)) ^ 5 < (𝒯.P i).h) ∧
  (𝒯.mode = .highSmall → ∀ i,
    ((𝒯.P i).h : ℝ) < Real.rpow ((𝒯.P i).d : ℝ) (1 / 40 : ℝ))

private abbrev allocation_retypePatch (T : Stage) (k : ℕ) (o : Bool) (P : Patch T k) :
    Patch (T.orient o) k := by
  cases o with
  | false => exact P
  | true =>
    exact { X := P.X, Y := P.Y, M := P.M, resX := P.resX, resY := P.resY, g := P.g, q := P.q, h := P.h, ℓ := P.ℓ, d := P.d, bins := P.bins, cardX := P.cardX, cardY := P.cardY, X_res := P.X_res, Y_res := P.Y_res }

private abbrev allocation_singleTiling (κ : CConsts) (T : Stage) (k : ℕ) (o : Bool)
    (mode : Mode) (c : Colour) (P : Patch T k)
    (ZX ZY : Finset (Fin (T.S.N k))) (Q : ℕ) : Tiling κ (T.orient o) k := by
  cases o with
  | false =>
    exact { mode := mode, c := c, m := 1, P := fun _ => P, S := P.M, w := fun _ _ => false, reserveX := ZX, reserveY := ZY, Q := fun _ => Q }
  | true =>
    exact { mode := mode, c := c, m := 1, P := fun _ => allocation_retypePatch T k true P, S := P.M, w := fun _ _ => false, reserveX := ZY, reserveY := ZX, Q := fun _ => Q }

private structure AllocationRawPass (κ : CConsts) (T : Stage) (k : ℕ)
    (ZX ZY : Finset (Fin (T.S.N k))) where
  orientation : Bool
  mode : Mode
  colour : Colour
  patch : Patch T k
  cliqueScale : ℕ
  nonbounded : mode ≠ .bounded
  data : ExtractionData (allocation_singleTiling κ T k orientation mode colour patch ZX ZY cliqueScale)

private def AllocationRawPass.physicalX {κ : CConsts} {T : Stage} {k : ℕ}
    {ZX ZY : Finset (Fin (T.S.N k))} (r : AllocationRawPass κ T k ZX ZY) :
    Finset (Fin (T.S.N k)) := if r.orientation then r.patch.Y else r.patch.X

private def AllocationRawPass.physicalY {κ : CConsts} {T : Stage} {k : ℕ}
    {ZX ZY : Finset (Fin (T.S.N k))} (r : AllocationRawPass κ T k ZX ZY) :
    Finset (Fin (T.S.N k)) := if r.orientation then r.patch.X else r.patch.Y

private theorem allocation_raw_mass {κ : CConsts} {T : Stage} {k : ℕ}
    {ZX ZY : Finset (Fin (T.S.N k))} (r : AllocationRawPass κ T k ZX ZY) :
    r.physicalX.card = r.patch.M ∧ r.physicalY.card = r.patch.M := by
  cases h : r.orientation <;> simp [AllocationRawPass.physicalX, AllocationRawPass.physicalY,
    h, r.patch.cardX, r.patch.cardY]

private theorem allocation_raw_nonempty {κ : CConsts} {T : Stage} {k : ℕ}
    {ZX ZY : Finset (Fin (T.S.N k))} (r : AllocationRawPass κ T k ZX ZY) :
    r.physicalX.Nonempty ∧ r.physicalY.Nonempty := by
  cases r with
  | mk o mode c P Q hmode hdata =>
    cases o
    · simpa [AllocationRawPass.physicalX, AllocationRawPass.physicalY,
        allocation_singleTiling, Stage.orient] using hdata.patch_nonempty 0
    · simpa [AllocationRawPass.physicalX, AllocationRawPass.physicalY,
        allocation_singleTiling, allocation_retypePatch, Stage.orient, Stage.swap, BadSeq.swap, and_comm]
        using hdata.patch_nonempty 0

private theorem allocation_raw_supports {κ : CConsts} {T : Stage} {k : ℕ}
    {ZX ZY : Finset (Fin (T.S.N k))} (r : AllocationRawPass κ T k ZX ZY) :
    r.physicalX ⊆ T.X k \ ZX ∧ r.physicalY ⊆ T.Y k \ ZY := by
  cases r with
  | mk o mode c P Q hmode hdata =>
    cases o
    · have h := hdata.patch_supports 0
      exact ⟨h.1.trans h.2.1, h.2.2.1.trans h.2.2.2⟩
    · have h := hdata.patch_supports 0
      exact ⟨h.2.2.1.trans h.2.2.2, h.1.trans h.2.1⟩

private noncomputable def allocation_emptyPatch (T : Stage) (k : ℕ) : Patch T k where
  X := ∅
  Y := ∅
  M := 0
  resX := ∅
  resY := ∅
  g := 1
  q := 1
  h := 0
  ℓ := 0
  d := 1
  bins := ⊥
  cardX := by simp
  cardY := by simp
  X_res := by simp
  Y_res := by simp

private theorem allocation_regroup_family (κ : CConsts) (T : Stage) (k : ℕ)
    (ZX ZY : Finset (Fin (T.S.N k)))
    (hZX : ZX.card = T.S.N k / 3) (hZY : ZY.card = T.S.N k / 3)
    (hZXT : ZX ⊆ T.X k) (hZYT : ZY ⊆ T.Y k)
    (s : Finset (AllocationRawPass κ T k ZX ZY))
    (hs : (s : Set (AllocationRawPass κ T k ZX ZY)).Pairwise (fun a b => Disjoint a.physicalX b.physicalX ∧ Disjoint a.physicalY b.physicalY))
    (o : Bool) (mode : Mode) (c : Colour) (hmode : mode ≠ .bounded) :
    ∃ f : PassFamily κ T k,
      f.orientation = o ∧ f.tiling.mode = mode ∧ f.tiling.c = c ∧
      f.tiling.S = ∑ r ∈ s.filter (fun r => (r.orientation, r.mode, r.colour) = (o, mode, c)), r.patch.M := by
  classical
  let A := s.filter fun r => (r.orientation, r.mode, r.colour) = (o, mode, c)
  let e : A ≃ Fin A.card := Fintype.equivFinOfCardEq (by simp)
  let idx : Fin A.card → AllocationRawPass κ T k ZX ZY := fun i => (e.symm i).val
  have hmem (i : Fin A.card) : idx i ∈ A := (e.symm i).property
  have htag (r : AllocationRawPass κ T k ZX ZY) (hr : r ∈ A) :
      r.orientation = o ∧ r.mode = mode ∧ r.colour = c := by
    have h := (Finset.mem_filter.mp hr).2
    simpa only [Prod.mk.injEq] using h
  have hidx (i j : Fin A.card) (hij : i ≠ j) : idx i ≠ idx j := by
    intro h
    apply hij
    apply e.symm.injective
    exact Subtype.ext h
  have hOne (i : Fin A.card) :
      ExtractionData (allocation_singleTiling κ T k o mode c (idx i).patch ZX ZY (idx i).cliqueScale) := by
    have ht := htag (idx i) (hmem i)
    cases hri : idx i with
    | mk ro rm rc rp rQ rNot rData =>
      have ht' : ro = o ∧ rm = mode ∧ rc = c := by simpa only [hri] using ht
      rcases ht' with ⟨rfl, rfl, rfl⟩
      exact rData
  have hDisj (a b : AllocationRawPass κ T k ZX ZY) (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
      Disjoint a.patch.X b.patch.X ∧ Disjoint a.patch.Y b.patch.Y := by
    have h := hs (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
    have hao := (htag a ha).1
    have hbo := (htag b hb).1
    cases o
    · simpa [AllocationRawPass.physicalX, AllocationRawPass.physicalY, hao, hbo] using h
    · simpa [AllocationRawPass.physicalX, AllocationRawPass.physicalY, hao, hbo, and_comm] using h
  have hSum : ∑ i : Fin A.card, (idx i).patch.M = ∑ r ∈ A, r.patch.M := by
    apply Finset.sum_bij (fun i _ => idx i)
    · intro i hi
      exact hmem i
    · intro i hi j hj hij
      by_contra hne
      exact hidx i j hne hij
    · intro r hr
      exact ⟨e ⟨r, hr⟩, Finset.mem_univ _, by simp [idx]⟩
    · intro i hi
      rfl
  have hSupper : ∑ r ∈ A, r.patch.M ≤ T.S.N k := by
    have hc : (A.biUnion fun r => r.patch.X).card = ∑ r ∈ A, r.patch.X.card := by
      apply Finset.card_biUnion
      intro a ha b hb hab
      exact (hDisj a b ha hb hab).1
    simp_rw [show ∀ r : AllocationRawPass κ T k ZX ZY, r.patch.X.card = r.patch.M from fun r => r.patch.cardX] at hc
    rw [← hc]
    simpa using Finset.card_le_univ (A.biUnion fun r => r.patch.X)
  let tiling : Tiling κ (T.orient o) k :=
    {allocation_singleTiling κ T k o mode c (allocation_emptyPatch T k) ZX ZY 0 with
      m := A.card
      P := fun i => allocation_retypePatch T k o (idx i).patch
      S := ∑ r ∈ A, r.patch.M
      w := fun _ _ => false
      Q := fun i => (idx i).cliqueScale}
  have hExtracted : ExtractionData tiling := by
    cases o <;> refine {
      reserveX_card := by first | simpa [tiling, allocation_singleTiling, Stage.orient, Stage.swap, BadSeq.swap] using hZX | simpa [tiling, allocation_singleTiling, Stage.orient, Stage.swap, BadSeq.swap] using hZY
      reserveY_card := by first | simpa [tiling, allocation_singleTiling, Stage.orient, Stage.swap, BadSeq.swap] using hZY | simpa [tiling, allocation_singleTiling, Stage.orient, Stage.swap, BadSeq.swap] using hZX
      reserveX_subset := by
        first
        | change ZX ⊆ T.X k
          exact hZXT
        | change ZY ⊆ T.Y k
          exact hZYT
      reserveY_subset := by
        first
        | change ZY ⊆ T.Y k
          exact hZYT
        | change ZX ⊆ T.X k
          exact hZXT
      patch_supports := by intro i; simpa [tiling, allocation_singleTiling, allocation_retypePatch, Stage.orient, Stage.swap, BadSeq.swap] using (hOne i).patch_supports 0
      patch_nonempty := by intro i; simpa [tiling, allocation_singleTiling, allocation_retypePatch, Stage.orient, Stage.swap, BadSeq.swap] using (hOne i).patch_nonempty 0
      bins_card := by intro i B hB; simpa [tiling, allocation_singleTiling, allocation_retypePatch, Stage.orient, Stage.swap, BadSeq.swap] using (hOne i).bins_card 0 B hB
      patch_X_disjoint := by
        intro i j hij
        change Disjoint (idx i).patch.X (idx j).patch.X
        exact (hDisj (idx i) (idx j) (hmem i) (hmem j) (hidx i j hij)).1
      patch_Y_disjoint := by
        intro i j hij
        change Disjoint (idx i).patch.Y (idx j).patch.Y
        exact (hDisj (idx i) (idx j) (hmem i) (hmem j) (hidx i j hij)).2
      S_upper := by simpa [tiling, Stage.orient, Stage.swap, BadSeq.swap] using hSupper
      measured_scales := by intro i; simpa [tiling, allocation_singleTiling, allocation_retypePatch, Stage.orient, Stage.swap, BadSeq.swap] using (hOne i).measured_scales 0
      bounded_scale_cutoff := by
        intro h
        have hm : mode = .bounded := by simpa [tiling, allocation_singleTiling, Stage.orient, Stage.swap, BadSeq.swap] using h
        exact (hmode hm).elim
      bounded_data := by intro h; simp [tiling, allocation_singleTiling, Stage.orient, Stage.swap, BadSeq.swap] at h; exact (hmode h).elim
      direct_scale_bound := by intro h i; simpa [tiling, allocation_singleTiling, allocation_retypePatch, Stage.orient, Stage.swap, BadSeq.swap] using (hOne i).direct_scale_bound h 0
      direct_data := by intro h i; simpa [tiling, allocation_singleTiling, allocation_retypePatch, Stage.orient, Stage.swap, BadSeq.swap] using (hOne i).direct_data h 0
      cluster_data := by intro h i; simpa [tiling, allocation_singleTiling, allocation_retypePatch, Stage.orient, Stage.swap, BadSeq.swap] using (hOne i).cluster_data h 0
      clique_scales := by intro i; simpa [tiling, allocation_singleTiling, allocation_retypePatch, Tiling.kScale] using (hOne i).clique_scales 0 }
  have hmass : ∑ i, (tiling.P i).M = tiling.S := by
    cases o <;> simpa [tiling, allocation_retypePatch, Stage.orient, Stage.swap, BadSeq.swap] using hSum
  exact ⟨{orientation := o, tiling := tiling, extracted := hExtracted, mass_sum := hmass},
    rfl, by cases o <;> rfl, by cases o <;> rfl, rfl⟩

private theorem allocation_regroup_collection (κ : CConsts) (T : Stage) (k : ℕ)
    (ZX ZY : Finset (Fin (T.S.N k)))
    (hZX : ZX.card = T.S.N k / 3) (hZY : ZY.card = T.S.N k / 3)
    (hZXT : ZX ⊆ T.X k) (hZYT : ZY ⊆ T.Y k)
    (s : Finset (AllocationRawPass κ T k ZX ZY))
    (hs : (s : Set (AllocationRawPass κ T k ZX ZY)).Pairwise (fun a b => Disjoint a.physicalX b.physicalX ∧ Disjoint a.physicalY b.physicalY))
    (hmass : (∑ r ∈ s, r.patch.M) * 10 ≥ T.S.N k) :
    Nonempty (PassCollection κ T k) := by
  classical
  let Tag := {t : Bool × Mode × Colour // t.2.1 ≠ .bounded}
  have hExists (t : Tag) := allocation_regroup_family κ T k ZX ZY hZX hZY hZXT hZYT
    s hs t.val.1 t.val.2.1 t.val.2.2 t.property
  choose family hfamily using hExists
  let tags : List Tag := (Finset.univ : Finset Tag).toList
  let families := tags.map family
  have htags : tags.Nodup := Finset.nodup_toList _
  have hType (t : Tag) :
      (family t).orientation = t.val.1 ∧ (family t).tiling.mode = t.val.2.1 ∧
        (family t).tiling.c = t.val.2.2 := by
    exact ⟨(hfamily t).1, (hfamily t).2.1, (hfamily t).2.2.1⟩
  have hNot (t : Tag) : (family t).tiling.mode ≠ .bounded := by
    rw [(hType t).2.1]
    exact t.property
  have hFilter : families.filter (fun f => f.tiling.mode ≠ .bounded) = families := by
    apply List.filter_eq_self.mpr
    intro f hf
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
    simp [hNot t]
  have hSum : (families.map fun f => f.tiling.S).sum = ∑ r ∈ s, r.patch.M := by
    change ((tags.map family).map fun f => f.tiling.S).sum = _
    rw [List.map_map]
    simp only [Function.comp_def]
    rw [← allocation_list_sum_toFinset (fun t => (family t).tiling.S) tags htags]
    have htagset : tags.toFinset = Finset.univ := by simp [tags]
    rw [htagset]
    simp_rw [(hfamily _).2.2.2]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    let t : Tag := ⟨(r.orientation, r.mode, r.colour), r.nonbounded⟩
    have hEq (u : Tag) : (r.orientation, r.mode, r.colour) = u.val ↔ u = t := by
      constructor
      · intro h
        exact Subtype.ext h.symm
      · intro h
        subst u
        rfl
    simpa only [hEq] using
      (Finset.sum_ite_eq_of_mem' (Finset.univ : Finset Tag) t (fun _ => r.patch.M) (Finset.mem_univ t))
  refine ⟨{families := families, families_mass := ?_, type_tags_nodup := ?_, mass_or_bounded := ?_}⟩
  · intro f hf
    exact f.mass_sum
  · change ((tags.map family).map fun f => (f.orientation, f.tiling.mode, f.tiling.c)).Nodup
    rw [List.map_map]
    simp only [Function.comp_def]
    have heq : (tags.map fun t => ((family t).orientation, (family t).tiling.mode, (family t).tiling.c)) =
        tags.map Subtype.val := by
      apply List.map_congr_left
      intro t ht
      simp only [(hType t).1, (hType t).2.1, (hType t).2.2]
    rw [heq]
    exact htags.map Subtype.val_injective
  · right
    rw [hFilter, hSum]
    exact hmass

private theorem allocation_bounded_collection (κ : CConsts) (T : Stage) (k : ℕ)
    (ZX ZY RX RY : Finset (Fin (T.S.N k)))
    (hZX : ZX.card = T.S.N k / 3) (hZY : ZY.card = T.S.N k / 3)
    (hZXT : ZX ⊆ T.X k) (hZYT : ZY ⊆ T.Y k)
    (hRX : RX ⊆ T.X k \ ZX) (hRY : RY ⊆ T.Y k \ ZY)
    (hCutoff : max (gScale κ T k RX RY : ℝ) (qScale κ T k RX RY : ℝ) < κ.M1 * κ.Q0)
    (X Y : Finset (Fin (T.S.N k))) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXR : X ⊆ RX) (hYR : Y ⊆ RY) (hcard : X.card = Y.card)
    (hM : (1 / 400 : ℝ) * T.S.N k ≤ X.card) : Nonempty (PassCollection κ T k) := by
  classical
  let P : Patch T k := {X := X, Y := Y, M := X.card, resX := RX, resY := RY, g := gScale κ T k RX RY, q := qScale κ T k RX RY, h := 0, ℓ := 0, d := 1, bins := ⊥, cardX := rfl, cardY := hcard.symm, X_res := hXR, Y_res := hYR}
  let tiling := allocation_singleTiling κ T k false .bounded false P ZX ZY κ.Qbd
  have hExtracted : ExtractionData tiling := by
    refine {
      reserveX_card := hZX
      reserveY_card := hZY
      reserveX_subset := hZXT
      reserveY_subset := hZYT
      patch_supports := by intro i; exact ⟨hXR, hRX, hYR, hRY⟩
      patch_nonempty := by intro i; exact ⟨hX, hY⟩
      bins_card := by
        intro i B hB
        change B ∈ (⊥ : Finpartition Y).parts at hB
        obtain ⟨y, hy, rfl⟩ := Finpartition.mem_bot_iff.mp hB
        change ({y} : Finset (Fin (T.S.N k))).card = 1
        exact Finset.card_singleton y
      patch_X_disjoint := by
        intro i j hij
        have hi : i.val < 1 := by simpa only [tiling, allocation_singleTiling, Stage.orient] using i.isLt
        have hj : j.val < 1 := by simpa only [tiling, allocation_singleTiling, Stage.orient] using j.isLt
        exact (hij (Fin.ext (by omega))).elim
      patch_Y_disjoint := by
        intro i j hij
        have hi : i.val < 1 := by simpa only [tiling, allocation_singleTiling, Stage.orient] using i.isLt
        have hj : j.val < 1 := by simpa only [tiling, allocation_singleTiling, Stage.orient] using j.isLt
        exact (hij (Fin.ext (by omega))).elim
      S_upper := by simpa [tiling, allocation_singleTiling, P, Stage.orient, Stage.swap, BadSeq.swap, Fintype.card_fin] using Finset.card_le_univ X
      measured_scales := by intro i; exact ⟨rfl, rfl⟩
      bounded_scale_cutoff := by intro hm i; simpa only [Nat.cast_max] using hCutoff
      bounded_data := by intro hm; exact ⟨rfl, fun i => ⟨rfl, rfl, rfl, hM, rfl⟩⟩
      direct_scale_bound := by simp [tiling, allocation_singleTiling, Stage.orient, Stage.swap, BadSeq.swap]
      direct_data := by simp [tiling, allocation_singleTiling, Stage.orient, Stage.swap, BadSeq.swap]
      cluster_data := by simp [tiling, allocation_singleTiling, Stage.orient, Stage.swap, BadSeq.swap]
      clique_scales := by simp [tiling, allocation_singleTiling, Stage.orient, Stage.swap, BadSeq.swap] }
  let f : PassFamily κ T k := {orientation := false, tiling := tiling, extracted := hExtracted, mass_sum := by simp [tiling, allocation_singleTiling, P, Stage.orient, Stage.swap, BadSeq.swap, Fintype.card_fin]}
  refine ⟨{families := [f], families_mass := ?_, type_tags_nodup := by simp, mass_or_bounded := ?_}⟩
  · intro g hg
    have hgf : g = f := by simpa using hg
    subst g
    exact f.mass_sum
  · left
    exact ⟨f, by simp, rfl, hM⟩

private theorem allocation_direct_clique (κ : CConsts) (hκ : κ.Admissible)
    (g q : ℕ) (hg : κ.M1 * κ.Q0 ≤ (g : ℝ)) (hq : κ.M1 * (q : ℝ) < g) :
    ∃ Q : ℕ, IsDyadic Q ∧ (g : ℝ) / (2 * Real.sqrt κ.M1) < Q ∧
      (Q : ℝ) ≤ 2 * g / Real.sqrt κ.M1 ∧ q < Q := by
  have hM : 0 < κ.M1 := by linarith [hκ.M1_big.1]
  have hs : 0 < Real.sqrt κ.M1 := Real.sqrt_pos.mpr hM
  have hs0 := hs.le
  have hsq := Real.sq_sqrt hM.le
  have hs2 : 2 ≤ Real.sqrt κ.M1 := by
    have ht := Real.sqrt_le_sqrt hκ.M1_big.1
    norm_num at ht
    exact ht
  have hsM : Real.sqrt κ.M1 ≤ κ.M1 := by nlinarith
  have htwos : 2 * Real.sqrt κ.M1 ≤ κ.M1 := by
    have hp := mul_nonneg hs0 (sub_nonneg.mpr hs2)
    nlinarith
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have hgM : κ.M1 ≤ (g : ℝ) := by
    have hQ0 := Lane_sol_s13_allocA.threshold hκ
    have hm := mul_le_mul_of_nonneg_left hQ0.le hM.le
    nlinarith
  have hx1 : 1 ≤ (g : ℝ) / Real.sqrt κ.M1 := (le_div_iff₀ hs).2 (by linarith)
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2)
  let Q : ℕ := 2 ^ j
  have hQcast : (Q : ℝ) = (2 : ℝ) ^ j := by simp [Q]
  have hLower : (g : ℝ) / (2 * Real.sqrt κ.M1) < Q := by
    rw [hQcast]
    rw [pow_succ] at hjhi
    have hmul := (div_lt_iff₀ hs).mp hjhi
    apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.sqrt κ.M1)).2
    nlinarith only [hmul]
  have hUpper : (Q : ℝ) ≤ 2 * g / Real.sqrt κ.M1 := by
    rw [hQcast]
    exact hjlo.trans (div_le_div_of_nonneg_right (by linarith : (g : ℝ) ≤ 2 * g) hs0)
  have hqLower : (q : ℝ) < (g : ℝ) / (2 * Real.sqrt κ.M1) := by
    have hqg : (q : ℝ) < (g : ℝ) / κ.M1 := (lt_div_iff₀ hM).2 (by simpa [mul_comm] using hq)
    exact hqg.trans_le (div_le_div_of_nonneg_left hg0 (by positivity) htwos)
  exact ⟨Q, ⟨j, rfl⟩, hLower, hUpper, by exact_mod_cast hqLower.trans hLower⟩

private theorem allocation_residual_card {N : ℕ} (W Z V : Finset (Fin N))
    (hZ : Z ⊆ W) (hV : V ⊆ W \ Z) (hZcard : Z.card = N / 3)
    (hSmall : (Wᶜ.card : ℝ) ≤ (N : ℝ) / 20)
    (hVcard : (V.card : ℝ) < (N : ℝ) / 10) :
    (N : ℝ) / 2 ≤ ((W \ Z) \ V).card := by
  have hWcard : W.card ≤ N := by simpa using Finset.card_le_univ W
  have hZle := Finset.card_le_card hZ
  have hVle := Finset.card_le_card hV
  have hDiff : (W \ Z).card = W.card - Z.card := Finset.card_sdiff_of_subset hZ
  have hRes : ((W \ Z) \ V).card = (W \ Z).card - V.card := Finset.card_sdiff_of_subset hV
  have hSum : ((W \ Z) \ V).card + V.card + Z.card = W.card := by omega
  have hCover : W.card + Wᶜ.card = N := by
    simp only [Finset.card_compl, Fintype.card_fin]
    omega
  have hZthree : 3 * Z.card ≤ N := by
    rw [hZcard]
    simpa [mul_comm] using Nat.div_mul_le_self N 3
  have hZr : (3 : ℝ) * Z.card ≤ N := by exact_mod_cast hZthree
  have hCoverr : (W.card : ℝ) + Wᶜ.card = N := by exact_mod_cast hCover
  have hSumr : (((W \ Z) \ V).card : ℝ) + V.card + Z.card = W.card := by exact_mod_cast hSum
  have hN0 : (0 : ℝ) ≤ N := by positivity
  linarith

private theorem allocation_direct_raw (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (ZX ZY RX RY : Finset (Fin (T.S.N k)))
    (hZX : ZX.card = T.S.N k / 3) (hZY : ZY.card = T.S.N k / 3)
    (hZXT : ZX ⊆ T.X k) (hZYT : ZY ⊆ T.Y k)
    (hRX : RX ⊆ T.X k \ ZX) (hRY : RY ⊆ T.Y k \ ZY)
    (g q : ℕ) (hg : g = gScale κ T k RX RY) (hq : q = qScale κ T k RX RY)
    (hCutoff : κ.M1 * κ.Q0 ≤ max (g : ℝ) (q : ℝ))
    (hgq : κ.M1 * (q : ℝ) < g) (hgbound : (g : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.ι / 2))
    (hPatch : DirectPatchData κ T k RX RY g) :
    ∃ r : AllocationRawPass κ T k ZX ZY, r.physicalX ⊆ RX ∧ r.physicalY ⊆ RY := by
  classical
  obtain ⟨c, X, Y, hX, hY, hXR, hYR, hcard, hM, hDegree⟩ := hPatch
  have hqg : (q : ℝ) ≤ g := by
    have hm1 := hκ.M1_big.1
    have hq0 : (0 : ℝ) ≤ q := by positivity
    nlinarith
  have hgmin : κ.M1 * κ.Q0 ≤ (g : ℝ) := by simpa [max_eq_left hqg] using hCutoff
  obtain ⟨Q, hQdyadic, hQlower, hQupper, hqQ⟩ := allocation_direct_clique κ hκ g q hgmin hgq
  let mode : Mode := if κ.KB * Real.log (T.S.n k) < g then .highDirect else .lowDirect
  have hnonbounded : mode ≠ .bounded := by dsimp [mode]; split <;> simp
  have hnoncluster : ¬ (mode = .lowCluster ∨ mode = .highSmall ∨ mode = .highLarge) := by
    dsimp [mode]; split <;> simp
  have hreg : (mode = .highDirect) ↔ κ.KB * Real.log (T.S.n k) < g := by
    dsimp [mode]; split <;> simp_all
  let P : Patch T k := {X := X, Y := Y, M := X.card, resX := RX, resY := RY, g := g, q := q, h := 0, ℓ := 0, d := 1, bins := ⊥, cardX := rfl, cardY := hcard.symm, X_res := hXR, Y_res := hYR}
  let tiling := allocation_singleTiling κ T k false mode c P ZX ZY Q
  have hExtracted : ExtractionData tiling := by
    refine {
      reserveX_card := hZX
      reserveY_card := hZY
      reserveX_subset := hZXT
      reserveY_subset := hZYT
      patch_supports := by intro i; exact ⟨hXR, hRX, hYR, hRY⟩
      patch_nonempty := by intro i; exact ⟨hX, hY⟩
      bins_card := by
        intro i B hB
        change B ∈ (⊥ : Finpartition Y).parts at hB
        obtain ⟨y, hy, rfl⟩ := Finpartition.mem_bot_iff.mp hB
        change ({y} : Finset (Fin (T.S.N k))).card = 1
        exact Finset.card_singleton y
      patch_X_disjoint := by
        intro i j hij
        have hi : i.val < 1 := by simpa only [tiling, allocation_singleTiling, Stage.orient] using i.isLt
        have hj : j.val < 1 := by simpa only [tiling, allocation_singleTiling, Stage.orient] using j.isLt
        exact (hij (Fin.ext (by omega))).elim
      patch_Y_disjoint := by
        intro i j hij
        have hi : i.val < 1 := by simpa only [tiling, allocation_singleTiling, Stage.orient] using i.isLt
        have hj : j.val < 1 := by simpa only [tiling, allocation_singleTiling, Stage.orient] using j.isLt
        exact (hij (Fin.ext (by omega))).elim
      S_upper := by simpa [tiling, allocation_singleTiling, P, Stage.orient, Stage.swap, BadSeq.swap, Fintype.card_fin] using Finset.card_le_univ X
      measured_scales := by intro i; exact ⟨hg, hq⟩
      bounded_scale_cutoff := by intro hm; exact (hnonbounded hm).elim
      bounded_data := by intro hm; exact (hnonbounded hm).elim
      direct_scale_bound := by intro hm i; exact hgbound
      direct_data := by
        intro hm i
        refine ⟨?_, hgq, hM, ?_, rfl, rfl, hreg⟩
        · simpa only [Nat.cast_max] using hCutoff
        · exact hDegree
      cluster_data := by intro hm; exact (hnoncluster hm).elim
      clique_scales := by
        intro i
        exact ⟨fun hm => (hnoncluster hm).elim, fun hm => ⟨hQdyadic, hQlower, hQupper, hqQ⟩⟩ }
  let r : AllocationRawPass κ T k ZX ZY := {orientation := false, mode := mode, colour := c, patch := P, cliqueScale := Q, nonbounded := hnonbounded, data := hExtracted}
  exact ⟨r, hXR, hYR⟩

private theorem allocation_bin_partition {N m d : ℕ} (Y : Finset (Fin N))
    (B : Fin m → Finset (Fin N)) (hd : 0 < d)
    (hSub : ∀ j, B j ⊆ Y) (hDisj : Set.PairwiseDisjoint Set.univ B)
    (hCard : ∀ j, (B j).card = d) (hUnion : Y = Finset.univ.biUnion B) :
    ∃ p : Finpartition Y, p.parts = Finset.univ.image B := by
  classical
  let parts := Finset.univ.image B
  have hpartsSub : ∀ p ∈ parts, p ⊆ Y := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    exact hSub j
  have hEmpty : ∅ ∉ parts := by
    intro h
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
    have hc := hCard j
    rw [he, Finset.card_empty] at hc
    omega
  have hUnique : ∀ y ∈ Y, ∃! p ∈ parts, y ∈ p := by
    intro y hy
    rw [hUnion] at hy
    obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.mp hy
    refine ⟨B j, ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hyj⟩, ?_⟩
    intro p hp
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hp.1
    have he : j' = j := by
      by_contra hne
      exact Finset.disjoint_left.mp (hDisj (Set.mem_univ _) (Set.mem_univ _) hne) hp.2 hyj
    rw [he]
  exact ⟨Finpartition.ofExistsUnique parts hpartsSub hUnique hEmpty, rfl⟩

private theorem allocation_maximal_collection (κ : CConsts) (T : Stage) (k : ℕ)
    (ZX ZY : Finset (Fin (T.S.N k)))
    (hZX : ZX.card = T.S.N k / 3) (hZY : ZY.card = T.S.N k / 3)
    (hZXT : ZX ⊆ T.X k) (hZYT : ZY ⊆ T.Y k)
    (hSmallX : ((T.X k)ᶜ.card : ℝ) ≤ (T.S.N k : ℝ) / 20)
    (hSmallY : ((T.Y k)ᶜ.card : ℝ) ≤ (T.S.N k : ℝ) / 20)
    (hOne : ∀ RX RY : Finset (Fin (T.S.N k)),
      RX ⊆ T.X k \ ZX → RY ⊆ T.Y k \ ZY →
      (T.S.N k : ℝ) / 2 ≤ RX.card → (T.S.N k : ℝ) / 2 ≤ RY.card →
      Nonempty (PassCollection κ T k) ∨
        ∃ r : AllocationRawPass κ T k ZX ZY, r.physicalX ⊆ RX ∧ r.physicalY ⊆ RY) :
    Nonempty (PassCollection κ T k) := by
  classical
  obtain ⟨s, hs, hMax⟩ := Lane_sol_s13_allocA.maximal_disjoint_patches
    (AllocationRawPass.physicalX (κ := κ) (T := T) (k := k) (ZX := ZX) (ZY := ZY))
    (AllocationRawPass.physicalY (κ := κ) (T := T) (k := k) (ZX := ZX) (ZY := ZY))
  let mass : ℕ := ∑ r ∈ s, r.patch.M
  let usedX := s.biUnion AllocationRawPass.physicalX
  let usedY := s.biUnion AllocationRawPass.physicalY
  have hCardX : usedX.card = mass := by
    have h := Finset.card_biUnion (s := s) (t := AllocationRawPass.physicalX)
      (fun a ha b hb hab => (hs ha hb hab).1)
    simpa only [usedX, mass, (allocation_raw_mass _).1] using h
  have hCardY : usedY.card = mass := by
    have h := Finset.card_biUnion (s := s) (t := AllocationRawPass.physicalY)
      (fun a ha b hb hab => (hs ha hb hab).2)
    simpa only [usedY, mass, (allocation_raw_mass _).2] using h
  have hUsedX : usedX ⊆ T.X k \ ZX := by
    intro x hx
    obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp hx
    exact (allocation_raw_supports r).1 hxr
  have hUsedY : usedY ⊆ T.Y k \ ZY := by
    intro y hy
    obtain ⟨r, hr, hyr⟩ := Finset.mem_biUnion.mp hy
    exact (allocation_raw_supports r).2 hyr
  by_cases hmass : T.S.N k ≤ mass * 10
  · exact allocation_regroup_collection κ T k ZX ZY hZX hZY hZXT hZYT s hs hmass
  · have hmassLt : mass * 10 < T.S.N k := lt_of_not_ge hmass
    have hmassR : (mass : ℝ) < (T.S.N k : ℝ) / 10 := by
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 10)).2
      exact_mod_cast hmassLt
    let RX := (T.X k \ ZX) \ usedX
    let RY := (T.Y k \ ZY) \ usedY
    have hRX : (T.S.N k : ℝ) / 2 ≤ RX.card :=
      allocation_residual_card (T.X k) ZX usedX hZXT hUsedX hZX hSmallX (by simpa [hCardX] using hmassR)
    have hRY : (T.S.N k : ℝ) / 2 ≤ RY.card :=
      allocation_residual_card (T.Y k) ZY usedY hZYT hUsedY hZY hSmallY (by simpa [hCardY] using hmassR)
    rcases hOne RX RY Finset.sdiff_subset Finset.sdiff_subset hRX hRY with hPool | ⟨r, hrX, hrY⟩
    · exact hPool
    · have hCross (a : AllocationRawPass κ T k ZX ZY) (ha : a ∈ s) :
          Disjoint r.physicalX a.physicalX ∧ Disjoint r.physicalY a.physicalY := by
        constructor
        · apply Finset.disjoint_left.mpr
          intro x hx hxa
          have hnot := (Finset.mem_sdiff.mp (hrX hx)).2
          exact hnot (Finset.mem_biUnion.mpr ⟨a, ha, hxa⟩)
        · apply Finset.disjoint_left.mpr
          intro y hy hya
          have hnot := (Finset.mem_sdiff.mp (hrY hy)).2
          exact hnot (Finset.mem_biUnion.mpr ⟨a, ha, hya⟩)
      have hNot : r ∉ s := by
        intro hr
        obtain ⟨x, hx⟩ := (allocation_raw_nonempty r).1
        exact Finset.disjoint_left.mp (hCross r hr).1 hx hx
      have hInsert : ((insert r s : Finset _) : Set (AllocationRawPass κ T k ZX ZY)).Pairwise
          (fun a b => Disjoint a.physicalX b.physicalX ∧ Disjoint a.physicalY b.physicalY) := by
        intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with haEq | haS
        · rcases Finset.mem_insert.mp hb with hbEq | hbS
          · subst a
            subst b
            exact (hab rfl).elim
          · subst a
            exact hCross b hbS
        · rcases Finset.mem_insert.mp hb with hbEq | hbS
          · subst b
            exact ⟨(hCross a haS).1.symm, (hCross a haS).2.symm⟩
          · exact hs haS hbS hab
      have hm := hMax (insert r s) hInsert
      rw [Finset.sum_insert hNot] at hm
      have hp : 0 < r.physicalX.card := Finset.card_pos.mpr (allocation_raw_nonempty r).1
      omega

private theorem allocation_cluster_clique (κ : CConsts) (hκ : κ.Admissible)
    (q h : ℕ) (hqDyadic : IsDyadic q) (hq : κ.Q0 ≤ (q : ℝ))
    (hlo : (q : ℝ) ^ (κ.Mlo : ℝ) ≤ h) (hhi : (h : ℝ) < 2 * (q : ℝ) ^ (κ.Mhi : ℝ)) :
    IsDyadic (q ^ 2) ∧ sliceK κ h < q ^ 2 := by
  have hqLarge := (Lane_sol_s13_allocA.cluster_scale_large hκ hq).1
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hh1r : (1 : ℝ) ≤ h :=
    (Real.one_le_rpow hq1 (Nat.cast_nonneg κ.Mlo)).trans hlo
  have hh1 : 1 ≤ h := by exact_mod_cast hh1r
  have hT : (1 : ℝ) ≤ sliceT κ h := by
    calc
      1 ≤ (h : ℝ) ^ κ.ω := Real.one_le_rpow hh1r hκ.ω_rng.1.le
      _ ≤ (⌈(h : ℝ) ^ κ.ω⌉₊ : ℝ) := Nat.le_ceil _
      _ = (sliceT κ h : ℝ) := by simp only [sliceT, Real.rpow_eq_pow]
  have hK : (sliceK κ h : ℝ) ≤ (sliceK κ h : ℝ) * sliceT κ h := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg (sliceK κ h))
  have htuple := Lane_sol_s13_allocA.cluster_tuple_bound hκ hq hhi hh1
  have hsmall : (q : ℝ) ^ (κ.aC / 2) < (q : ℝ) ^ (2 : ℕ) := by
    calc
      _ < (q : ℝ) ^ (2 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by linarith)
        (by linarith [(Lane_sol_s13_allocA.parameters hκ).2.2.2.1])
      _ = _ := by norm_num only [Real.rpow_ofNat]
  have hKR : (sliceK κ h : ℝ) < (q : ℝ) ^ (2 : ℕ) := hK.trans_lt (htuple.trans_lt hsmall)
  rcases hqDyadic with ⟨j, hj⟩
  exact ⟨⟨j * 2, by rw [hj, pow_mul]⟩, by exact_mod_cast hKR⟩

private theorem allocation_gScale_swap (κ : CConsts) (T : Stage) (k : ℕ)
    (RX RY : Finset (Fin (T.S.N k))) :
    gScale κ T.swap k RY RX = gScale κ T k RX RY := by
  classical
  unfold gScale
  apply congrArg (fun J : Finset ℕ => 2 ^ J.sup id)
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [biasWitness_swap_iff]
  rfl

set_option maxHeartbeats 1600000 in
private theorem allocation_cluster_raw (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (ZX ZY RX RY : Finset (Fin (T.S.N k)))
    (hZX : ZX.card = T.S.N k / 3) (hZY : ZY.card = T.S.N k / 3)
    (hZXT : ZX ⊆ T.X k) (hZYT : ZY ⊆ T.Y k)
    (hRX : RX ⊆ T.X k \ ZX) (hRY : RY ⊆ T.Y k \ ZY)
    (g q : ℕ) (o : Bool) (hg : g = gScale κ T k RX RY) (hq : q = qScale κ T k RX RY)
    (hCutoff : κ.M1 * κ.Q0 ≤ max (g : ℝ) (q : ℝ)) (hgq : (g : ℝ) ≤ κ.M1 * q)
    (hqmin : κ.Q0 ≤ (q : ℝ)) (hqDyadic : IsDyadic q)
    (hLCutoff : (Real.log (T.S.n k)) ^ κ.cq ≤ (Real.log (T.S.n k)) ^ 2)
    (hNode : ∀ d : ℕ, 0 < d → (d : ℝ) ≤ Real.exp ((q : ℝ) / 2) →
      ClusterPatchData κ T k RX RY q o d) :
    ∃ r : AllocationRawPass κ T k ZX ZY, r.physicalX ⊆ RX ∧ r.physicalY ⊆ RY := by
  classical
  let L : ℝ := Real.log (T.S.n k)
  let mode : Mode := if (q : ℝ) ≤ L ^ κ.cq then .lowCluster else
    if (q : ℝ) ≤ L ^ 2 then .highSmall else .highLarge
  let d : ℕ := if mode = .highSmall then
    min ⌊Real.exp ((q : ℝ) / 2)⌋₊ ⌊Real.exp (Real.sqrt L)⌋₊ else ⌊Real.exp ((q : ℝ) / 2)⌋₊
  let M : ℕ := if mode = .lowCluster then κ.Mlo else κ.Mhi
  let h : ℕ := q ^ M
  have hqLarge := (Lane_sol_s13_allocA.cluster_scale_large hκ hqmin).1
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hq0 : 0 < q := by exact_mod_cast (show (0 : ℝ) < q by linarith)
  have hMF := Lane_sol_s13_allocA.Mhi_positive hκ
  have hnonbounded : mode ≠ .bounded := by dsimp [mode]; split_ifs <;> simp
  have hnondirect : ¬ (mode = .lowDirect ∨ mode = .highDirect) := by dsimp [mode]; split_ifs <;> simp
  have hregLow : mode = .lowCluster ↔ (q : ℝ) ≤ L ^ κ.cq := by
    dsimp [mode]; split_ifs <;> simp_all only [eq_self_iff_true, reduceCtorEq, true_iff, false_iff]
  have hregSmall : mode = .highSmall ↔ L ^ κ.cq < (q : ℝ) ∧ (q : ℝ) ≤ L ^ 2 := by
    by_cases ha : (q : ℝ) ≤ L ^ κ.cq
    · simp [mode, ha, not_lt_of_ge ha]
    · by_cases hb : (q : ℝ) ≤ L ^ 2
      · simp [mode, ha, hb, lt_of_not_ge ha]
      · simp [mode, ha, hb]
  have hregLarge : mode = .highLarge ↔ L ^ 2 < (q : ℝ) := by
    by_cases ha : (q : ℝ) ≤ L ^ κ.cq
    · have hb : (q : ℝ) ≤ L ^ 2 := ha.trans hLCutoff
      simp [mode, ha, not_lt_of_ge hb]
    · by_cases hb : (q : ℝ) ≤ L ^ 2
      · simp [mode, ha, hb, not_lt_of_ge hb]
      · simp [mode, ha, hb, lt_of_not_ge hb]
  have hdFull : 0 < ⌊Real.exp ((q : ℝ) / 2)⌋₊ :=
    Nat.floor_pos.mpr (Real.one_le_exp_iff.mpr (by positivity))
  have hdSmall : 0 < ⌊Real.exp (Real.sqrt L)⌋₊ :=
    Nat.floor_pos.mpr (Real.one_le_exp_iff.mpr (Real.sqrt_nonneg _))
  have hd : 0 < d := by dsimp [d]; split_ifs <;> first | exact lt_min hdFull hdSmall | exact hdFull
  have hdle : d ≤ ⌊Real.exp ((q : ℝ) / 2)⌋₊ := by
    dsimp [d]; split_ifs <;> first | exact Nat.min_le_left _ _ | exact le_rfl
  have hdCast : (d : ℝ) ≤ (⌊Real.exp ((q : ℝ) / 2)⌋₊ : ℝ) := by exact_mod_cast hdle
  have hdReal : (d : ℝ) ≤ Real.exp ((q : ℝ) / 2) :=
    hdCast.trans (Nat.floor_le (Real.exp_pos _).le)
  obtain ⟨X, Y, m, B, hX, hY, hd', hXR, hYR, hXY, hSize,
    hBsub, hBdisj, hBcard, hUnion, hCodegree⟩ := hNode d hd hdReal
  obtain ⟨bins, hbins⟩ := allocation_bin_partition Y B hd hBsub hBdisj hBcard hUnion
  have hDimEq : (q : ℝ) ^ (M : ℝ) = (h : ℝ) := by simp only [h, Real.rpow_natCast, Nat.cast_pow]
  have hMlo : (κ.Mlo : ℝ) ≤ M := by dsimp [M]; split_ifs <;> first | exact le_rfl | exact hMF.2.2
  have hMhi : (M : ℝ) ≤ κ.Mhi := by dsimp [M]; split_ifs <;> first | exact hMF.2.2 | exact le_rfl
  have hhlo : (q : ℝ) ^ (κ.Mlo : ℝ) ≤ h :=
    (Real.rpow_le_rpow_of_exponent_le hq1 hMlo).trans hDimEq.le
  have hh1 : (1 : ℝ) ≤ h := (Real.one_le_rpow hq1 (Nat.cast_nonneg κ.Mlo)).trans hhlo
  have hhhi : (h : ℝ) < 2 * (q : ℝ) ^ (κ.Mhi : ℝ) := by
    have hh := hDimEq.symm.le.trans (Real.rpow_le_rpow_of_exponent_le hq1 hMhi)
    have hp : 0 < (q : ℝ) ^ (κ.Mhi : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    linarith
  obtain ⟨j, hj⟩ := hqDyadic
  have hPow : h = 2 ^ (j * M) := by simp only [h, hj, pow_mul]
  have hDyadic : h = 2 ^ Nat.log2 h := by
    rw [hPow, Nat.log2_eq_log_two, Nat.log_pow (by decide : 1 < (2 : ℕ))]
  obtain ⟨hQdyadic, hKQ⟩ := allocation_cluster_clique κ hκ q h ⟨j, hj⟩ hqmin hhlo hhhi
  let P : Patch T k := {
    X := X, Y := Y, M := X.card, resX := if o then RY else RX, resY := if o then RX else RY,
    g := g, q := q, h := h, ℓ := 0, d := d, bins := bins,
    cardX := rfl, cardY := hXY.symm, X_res := hXR, Y_res := hYR }
  let tiling := allocation_singleTiling κ T k o mode true P ZX ZY (q ^ 2)
  have hExtracted : ExtractionData tiling := by
    cases o <;> refine {
      reserveX_card := by first | exact hZX | exact hZY
      reserveY_card := by first | exact hZY | exact hZX
      reserveX_subset := by first | exact hZXT | exact hZYT
      reserveY_subset := by first | exact hZYT | exact hZXT
      patch_supports := by intro i; first | exact ⟨hXR, hRX, hYR, hRY⟩ | exact ⟨hXR, hRY, hYR, hRX⟩
      patch_nonempty := by intro i; exact ⟨hX, hY⟩
      bins_card := by
        intro i b hb
        change b ∈ bins.parts at hb
        rw [hbins] at hb
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
        exact hBcard j
      patch_X_disjoint := by
        intro i j hij
        have hi : i.val < 1 := i.isLt
        have hj : j.val < 1 := j.isLt
        exact (hij (Fin.ext (by omega))).elim
      patch_Y_disjoint := by
        intro i j hij
        have hi : i.val < 1 := i.isLt
        have hj : j.val < 1 := j.isLt
        exact (hij (Fin.ext (by omega))).elim
      S_upper := by change X.card ≤ T.S.N k; simpa using Finset.card_le_univ X
      measured_scales := by
        intro i
        first
        | exact ⟨hg, hq⟩
        | constructor
          · change g = gScale κ T.swap k RY RX
            rw [allocation_gScale_swap]
            exact hg
          · change q = qScale κ T.swap k RY RX
            rw [Lane_sol_s13_allocA.qScale_swap]
            exact hq
      bounded_scale_cutoff := by intro hm; exact (hnonbounded hm).elim
      bounded_data := by intro hm; exact (hnonbounded hm).elim
      direct_scale_bound := by intro hm; exact (hnondirect hm).elim
      direct_data := by intro hm; exact (hnondirect hm).elim
      cluster_data := by
        intro hm i
        refine ⟨?_, hgq, hSize, ?_, ?_, ?_, hDyadic, ?_, ?_, ?_, ?_, ?_⟩
        · simpa only [Nat.cast_max] using hCutoff
        · intro hsmall
          change mode = .highSmall at hsmall
          change d = min ⌊Real.exp ((q : ℝ) / 2)⌋₊ ⌊Real.exp (Real.sqrt L)⌋₊
          simp only [d, hsmall, if_pos]
        · intro hother
          change mode = .lowCluster ∨ mode = .highLarge at hother
          change d = ⌊Real.exp ((q : ℝ) / 2)⌋₊
          rcases hother with hlow | hlarge
          · simp [d, hlow]
          · simp [d, hlarge]
        · intro b hb y hy y' hy'
          change b ∈ bins.parts at hb
          rw [hbins] at hb
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
          simpa only [Stage.orient, Stage.swap, BadSeq.swap, Bool.false_eq_true, if_false, if_true]
            using hCodegree j y y' hy hy'
        · change (q : ℝ) ^ (if mode = .lowCluster then (κ.Mlo : ℝ) else κ.Mhi) ≤ (h : ℝ)
          by_cases hl : mode = .lowCluster <;> simpa [M, hl, Real.rpow_eq_pow] using hDimEq.le
        · change (h : ℝ) < 2 * (q : ℝ) ^ (if mode = .lowCluster then (κ.Mlo : ℝ) else κ.Mhi)
          have hh : (h : ℝ) < 2 * (q : ℝ) ^ (M : ℝ) := by rw [hDimEq]; linarith
          by_cases hl : mode = .lowCluster <;> simpa [M, hl, Real.rpow_eq_pow] using hh
        · simpa only [L, Stage.orient, Stage.swap, BadSeq.swap, Real.rpow_eq_pow] using hregLow
        · simpa only [L, Stage.orient, Stage.swap, BadSeq.swap, Real.rpow_eq_pow] using hregSmall
        · simpa only [L, Stage.orient, Stage.swap, BadSeq.swap] using hregLarge
      clique_scales := by
        intro i
        constructor
        · intro hm
          refine ⟨hQdyadic, le_rfl, ?_, hKQ⟩
          change ((q ^ 2 : ℕ) : ℝ) ≤ 2 * (q : ℝ) ^ (2 : ℕ)
          simp only [Nat.cast_pow]
          nlinarith [sq_nonneg (q : ℝ)]
        · intro hm
          exact (hnondirect hm).elim }
  let r : AllocationRawPass κ T k ZX ZY := {
    orientation := o, mode := mode, colour := true, patch := P, cliqueScale := q ^ 2,
    nonbounded := hnonbounded, data := hExtracted }
  cases o
  · exact ⟨r, hXR, hYR⟩
  · exact ⟨r, hYR, hXR⟩

set_option maxHeartbeats 1600000 in
/-- P13.3d (sections/13, lines 128–159): residual scales and patch nodes drive repeated extraction passes. -/
theorem extraction_passes (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : DeepDisc T κ.xs κ.α 0.04)
    (hDeepι : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hClu : ClusterAbsenceInput κ T)
    (hSamplingU : UniformSubsampleStatement)
    (hBiasNode : ∀ᶠ k in atTop, ∀ (RX RY : Finset (Fin (T.S.N k))) (g : ℕ),
      RX ⊆ T.X k → RY ⊆ T.Y k →
      κ.M1 * κ.Q0 ≤ (g : ℝ) → BiasWitness κ T k RX RY g →
      ¬ BiasWitness κ T k RX RY (2 * g) → DirectPatchData κ T k RX RY g)
    (hClusterNode : ∀ᶠ k in atTop, ∀ (RX RY : Finset (Fin (T.S.N k))) (q : ℕ) (o : Bool),
      RX ⊆ T.X k → RY ⊆ T.Y k →
      IsDyadic q → κ.Q0 ≤ (q : ℝ) → CluScaleWitness κ T k RX RY q o →
      ∀ d : ℕ, 0 < d → (d : ℝ) ≤ Real.exp ((q : ℝ) / 2) →
        ClusterPatchData κ T k RX RY q o d)
    (hBoundedNode : ∀ k RX RY,
      (T.S.N k : ℝ) / 2 ≤ RX.card → (T.S.N k : ℝ) / 2 ≤ RY.card →
      ∃ X Y : Finset (Fin (T.S.N k)), X.Nonempty ∧ Y.Nonempty ∧
        X ⊆ RX ∧ Y ⊆ RY ∧ X.card = Y.card ∧
        (1 / 400 : ℝ) * T.S.N k ≤ X.card)
    (hScaleSpec : ResidualScaleSpec)
    (hScaleBounds : ResidualScaleBoundFacts κ T) :
    ∀ᶠ k in atTop, Nonempty (PassCollection κ T k) := by
  classical
  have hQ0 := Lane_sol_s13_allocA.threshold hκ
  have hM1 : 0 < κ.M1 := by linarith [hκ.M1_big.1]
  have hMlo := (Lane_sol_s13_allocA.Mhi_positive hκ).1
  have hMloR : (1 : ℝ) ≤ κ.Mlo := by
    have hn : 1 ≤ κ.Mlo := by omega
    exact_mod_cast hn
  have hcq : κ.cq ≤ 2 := by
    have hc := (lt_div_iff₀ (by positivity : (0 : ℝ) < 20 * (κ.Mlo : ℝ))).mp hκ.cq_rng.2
    have hm := mul_le_mul_of_nonneg_left hMloR hκ.cq_rng.1.le
    nlinarith
  have hι : κ.ι / 2 ≤ 1 := by
    have hm : min κ.xs (min κ.η0 (0.01 : ℝ)) ≤ 0.01 :=
      (min_le_right _ _).trans (min_le_right _ _)
    nlinarith [hκ.ι_rng.2]
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  have hlog : Tendsto (fun k => Real.log (T.S.n k)) atTop atTop := by
    simpa only [Function.comp_def] using Real.tendsto_log_atTop.comp hn
  have hsmall := T.small.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))
  filter_upwards [hBiasNode, hClusterNode, (hScaleBounds 1 (by norm_num)).1,
    hsmall, hn.eventually_ge_atTop 1, hlog.eventually_ge_atTop 1]
    with k hBias hCluster hG hSmall hn1 hLog1
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hsmallSum : (((T.X k)ᶜ.card : ℝ) + (T.Y k)ᶜ.card) < (T.S.N k : ℝ) / 20 := by
    have hm := (div_lt_iff₀ hN).mp hSmall
    push_cast at hm
    linarith
  have hSmallX : ((T.X k)ᶜ.card : ℝ) ≤ (T.S.N k : ℝ) / 20 := by
    have hy : (0 : ℝ) ≤ (T.Y k)ᶜ.card := by positivity
    linarith
  have hSmallY : ((T.Y k)ᶜ.card : ℝ) ≤ (T.S.N k : ℝ) / 20 := by
    have hx : (0 : ℝ) ≤ (T.X k)ᶜ.card := by positivity
    linarith
  have hreserve (W : Finset (Fin (T.S.N k))) (hW : (Wᶜ.card : ℝ) ≤ (T.S.N k : ℝ) / 20) :
      T.S.N k / 3 ≤ W.card := by
    have hWle : W.card ≤ T.S.N k := by simpa using Finset.card_le_univ W
    have hcover : W.card + Wᶜ.card = T.S.N k := by
      simp only [Finset.card_compl, Fintype.card_fin]
      omega
    have hcoverR : (W.card : ℝ) + Wᶜ.card = T.S.N k := by exact_mod_cast hcover
    have hthree : 3 * (T.S.N k / 3) ≤ T.S.N k := by
      simpa [mul_comm] using Nat.div_mul_le_self (T.S.N k) 3
    have hthreeR : (3 : ℝ) * (T.S.N k / 3 : ℕ) ≤ T.S.N k := by exact_mod_cast hthree
    exact_mod_cast (show ((T.S.N k / 3 : ℕ) : ℝ) ≤ W.card by linarith)
  obtain ⟨ZX, hZXT, hZX⟩ := Finset.exists_subset_card_eq (hreserve (T.X k) hSmallX)
  obtain ⟨ZY, hZYT, hZY⟩ := Finset.exists_subset_card_eq (hreserve (T.Y k) hSmallY)
  apply allocation_maximal_collection κ T k ZX ZY hZX hZY hZXT hZYT hSmallX hSmallY
  intro RX RY hRX hRY hRXcard hRYcard
  have hRXT := hRX.trans Finset.sdiff_subset
  have hRYT := hRY.trans Finset.sdiff_subset
  let g := gScale κ T k RX RY
  let q := qScale κ T k RX RY
  by_cases hbounded : max (g : ℝ) (q : ℝ) < κ.M1 * κ.Q0
  · obtain ⟨X, Y, hX, hY, hXR, hYR, hXY, hSize⟩ := hBoundedNode k RX RY hRXcard hRYcard
    exact Or.inl (allocation_bounded_collection κ T k ZX ZY RX RY hZX hZY hZXT hZYT
      hRX hRY hbounded X Y hX hY hXR hYR hXY hSize)
  · have hCutoff : κ.M1 * κ.Q0 ≤ max (g : ℝ) (q : ℝ) := le_of_not_gt hbounded
    by_cases hDirect : κ.M1 * (q : ℝ) < g
    · have hqg : (q : ℝ) ≤ g := by
        have hq0 : (0 : ℝ) ≤ q := by positivity
        nlinarith [hκ.M1_big.1]
      have hgmin : κ.M1 * κ.Q0 ≤ (g : ℝ) := by simpa only [max_eq_left hqg] using hCutoff
      have hg2r : (2 : ℝ) ≤ g := by
        have hm := mul_le_mul_of_nonneg_left hQ0.le hM1.le
        nlinarith [hκ.M1_big.1]
      have hg2 : 2 ≤ g := by exact_mod_cast hg2r
      have hgBound : (g : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) := (hG RX RY hRXT hRYT).2
      have hgN : g ≤ T.S.n k := by
        have hp : (T.S.n k : ℝ) ^ (κ.ι / 2) ≤ (T.S.n k : ℝ) := by
          calc
            _ ≤ (T.S.n k : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hι
            _ = _ := Real.rpow_one _
        exact_mod_cast hgBound.trans hp
      have hgd := hScaleSpec.g_dyadic κ T k RX RY
      have hgd2 : IsDyadic (2 * g) := by
        obtain ⟨j, hj⟩ := hgd
        refine ⟨j + 1, ?_⟩
        change 2 * g = 2 ^ (j + 1)
        change g = 2 ^ j at hj
        simp [hj, pow_succ, Nat.mul_comm]
      have hWitness : BiasWitness κ T k RX RY g := hScaleSpec.bias_witness κ T k RX RY hg2
      have hAbsent : ¬ BiasWitness κ T k RX RY (2 * g) :=
        hScaleSpec.bias_absent κ T k RX RY (2 * g) hgd2 (by omega) (by omega)
      have hPatch := hBias RX RY g hRXT hRYT hgmin hWitness hAbsent
      right
      exact allocation_direct_raw κ hκ T k ZX ZY RX RY hZX hZY hZXT hZYT hRX hRY
        g q rfl rfl hCutoff hDirect hgBound hPatch
    · have hgq : (g : ℝ) ≤ κ.M1 * q := le_of_not_gt hDirect
      have hqmin : κ.Q0 ≤ (q : ℝ) := by
        have hq0 : (0 : ℝ) ≤ q := by positivity
        have hqq : (q : ℝ) ≤ κ.M1 * q := by nlinarith [hκ.M1_big.1]
        have hm := hCutoff.trans (max_le hgq hqq)
        exact (mul_le_mul_iff_right₀ hM1).mp hm
      have hq2 : 2 ≤ q := by
        have hq1 : (1 : ℝ) < q := hQ0.trans_le hqmin
        have hq1n : 1 < q := by exact_mod_cast hq1
        omega
      obtain ⟨o, hWitness⟩ := hScaleSpec.cluster_witness κ T k RX RY hq2
      have hNode := hCluster RX RY q o hRXT hRYT (hScaleSpec.q_dyadic κ T k RX RY) hqmin hWitness
      have hLCutoff : (Real.log (T.S.n k)) ^ κ.cq ≤ (Real.log (T.S.n k)) ^ 2 := by
        calc
          _ ≤ (Real.log (T.S.n k)) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hLog1 hcq
          _ = _ := by norm_num only [Real.rpow_ofNat]
      right
      exact allocation_cluster_raw κ hκ T k ZX ZY RX RY hZX hZY hZXT hZYT hRX hRY
        g q o rfl rfl hCutoff hgq hqmin (hScaleSpec.q_dyadic κ T k RX RY) hLCutoff hNode

/-- P13.3e (sections/13, lines 159–168): select one bounded family or a nonbounded type carrying at least
one twentieth of the extracted mass. -/
theorem type_selection (κ : CConsts) (T : Stage) (k : ℕ)
    (families : List (PassFamily κ T k))
    (hFamilyMass : ∀ f ∈ families, ∑ i, (f.tiling.P i).M = f.tiling.S)
    (htags : (families.map fun f : PassFamily κ T k =>
      (f.orientation, f.tiling.mode, f.tiling.c)).Nodup)
    (hmass : (∃ f ∈ families, f.tiling.mode = .bounded ∧
      (1 / 400 : ℝ) * T.S.N k ≤ f.tiling.S) ∨
      ((families.filter fun f => f.tiling.mode ≠ .bounded).map
        (fun f => f.tiling.S)).sum * 10 ≥ T.S.N k) :
    ∃ f : PassFamily κ T k, f ∈ families ∧
      ((f.tiling.mode = .bounded ∧ (1 / 400 : ℝ) * T.S.N k ≤ f.tiling.S) ∨
       (f.tiling.mode ≠ .bounded ∧ (1 / 200 : ℝ) * T.S.N k ≤ f.tiling.S)) := by
  classical
  rcases hmass with hbounded | hnonbounded
  · rcases hbounded with ⟨f, hf, hmode, hsize⟩
    exact ⟨f, hf, Or.inl ⟨hmode, hsize⟩⟩
  · let tag : PassFamily κ T k → Bool × Mode × Colour :=
      fun f => (f.orientation, f.tiling.mode, f.tiling.c)
    let L := families.filter fun f => f.tiling.mode ≠ .bounded
    have htagsL : (L.map tag).Nodup := by
      apply List.Nodup.sublist _ htags
      exact (List.filter_sublist).map tag
    let possible : Finset (Bool × Mode × Colour) :=
      Finset.univ.filter fun t => t.2.1 ≠ .bounded
    have hpossible : possible.card = 20 := by
      decide
    have hlen : L.length ≤ 20 := by
      let s := (L.map tag).toFinset
      have hs : s ⊆ possible := by
        intro t ht
        rcases List.mem_toFinset.mp ht with ht
        rcases List.mem_map.mp ht with ⟨f, hf, rfl⟩
        simp only [possible, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [L] using (List.mem_filter.mp hf).2
      calc
        L.length = s.card := by
          simpa [s] using (List.toFinset_card_of_nodup htagsL).symm
        _ ≤ possible.card := Finset.card_le_card hs
        _ = 20 := hpossible
    have hNpos : 0 < T.S.N k := T.S.N_pos k
    have hmassNat : (L.map fun f => f.tiling.S).sum * 10 ≥ T.S.N k := by
      simpa [L] using hnonbounded
    have hLne : L ≠ [] := by
      intro hnil
      simp [hnil] at hmassNat
      omega
    by_contra hnone
    have hsmall : ∀ f ∈ L, (f.tiling.S : ℝ) < (1 / 200 : ℝ) * T.S.N k := by
      intro f hf
      rcases (show f ∈ families ∧ f.tiling.mode ≠ .bounded by simpa [L] using hf) with
        ⟨hfam, hmode⟩
      have hnot : ¬ (1 / 200 : ℝ) * T.S.N k ≤ f.tiling.S := by
        intro hs
        exact hnone ⟨f, hfam, Or.inr ⟨hmode, hs⟩⟩
      exact lt_of_not_ge hnot
    have hsum_bound : ∀ xs : List (PassFamily κ T k),
        (∀ f ∈ xs, (f.tiling.S : ℝ) < (1 / 200 : ℝ) * T.S.N k) →
        (xs.map fun f => (f.tiling.S : ℝ)).sum ≤
          (xs.length : ℝ) * ((1 / 200 : ℝ) * T.S.N k) := by
      intro xs
      induction xs with
      | nil => simp
      | cons a xs ih =>
        intro hall
        have ha := hall a (by simp)
        have htail := ih (by
          intro f hf
          exact hall f (by simp [hf]))
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [Nat.cast_add, Nat.cast_one]
        calc
          _ ≤ (1 / 200 : ℝ) * T.S.N k + (xs.map fun f => (f.tiling.S : ℝ)).sum :=
            add_le_add_left ha.le _
          _ ≤ (1 / 200 : ℝ) * T.S.N k +
              (xs.length : ℝ) * ((1 / 200 : ℝ) * T.S.N k) :=
            add_le_add_right htail _
          _ = ((xs.length : ℝ) + 1) * ((1 / 200 : ℝ) * T.S.N k) := by ring
    obtain ⟨f₀, xs, hLdef⟩ := List.exists_cons_of_ne_nil hLne
    have hhead : (f₀.tiling.S : ℝ) < (1 / 200 : ℝ) * T.S.N k := by
      apply hsmall f₀
      rw [hLdef]
      simp
    have htail := hsum_bound xs (by
      intro f hf
      apply hsmall f
      rw [hLdef]
      exact List.mem_cons_of_mem _ hf)
    have hsumlt : (L.map fun f => (f.tiling.S : ℝ)).sum <
        (L.length : ℝ) * ((1 / 200 : ℝ) * T.S.N k) := by
      rw [hLdef]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.cast_add, Nat.cast_one]
      apply lt_of_lt_of_le
      · exact add_lt_add_left hhead _
      · calc
          _ ≤ (1 / 200 : ℝ) * T.S.N k +
              (xs.length : ℝ) * ((1 / 200 : ℝ) * T.S.N k) :=
            add_le_add_right htail _
          _ = ((xs.length : ℝ) + 1) * ((1 / 200 : ℝ) * T.S.N k) := by ring
    have hlenR : (L.length : ℝ) ≤ 20 := by exact_mod_cast hlen
    have hmassR : (T.S.N k : ℝ) ≤
        (L.map fun f => (f.tiling.S : ℝ)).sum * 10 := by
      have hc : (T.S.N k : ℝ) ≤
          (((L.map fun f => f.tiling.S).sum * 10 : ℕ) : ℝ) := by
        exact_mod_cast hmassNat
      simpa [Nat.cast_mul, Nat.cast_sum, List.map_map, Function.comp_def] using hc
    have hsumSmall : (L.map fun f => (f.tiling.S : ℝ)).sum * 10 <
        (T.S.N k : ℝ) := by
      have htarget : 0 ≤ (1 / 200 : ℝ) * T.S.N k := by positivity
      calc
        _ < ((L.length : ℝ) * ((1 / 200 : ℝ) * T.S.N k)) * 10 :=
          mul_lt_mul_of_pos_right hsumlt (by norm_num)
        _ ≤ (20 : ℝ) * ((1 / 200 : ℝ) * T.S.N k) * 10 := by
          gcongr
        _ = T.S.N k := by ring
    exact (not_lt_of_ge hmassR) hsumSmall
    

set_option maxHeartbeats 5000000 in
/-- P13.3f (sections/13, lines 170–182): round dyadic masses upward and retain the first complete segment. -/
theorem dyadic_rounding (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (f : PassFamily κ T k)
    (hExtracted : ExtractionData f.tiling)
    (hSelected : (f.tiling.mode = .bounded ∧ (1 / 400 : ℝ) * T.S.N k ≤ f.tiling.S) ∨
       (f.tiling.mode ≠ .bounded ∧ (1 / 200 : ℝ) * T.S.N k ≤ f.tiling.S)) :
    ∃ R : RoundedFamily κ T k, Nonempty (RoundingProvenance f R) := by
  classical
  have hNpos : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hSpos : 0 < (f.tiling.S : ℝ) := by
    rcases hSelected with ⟨_, hsize⟩ | ⟨_, hsize⟩
    · exact lt_of_lt_of_le (mul_pos (by norm_num) hNpos) hsize
    · exact lt_of_lt_of_le (mul_pos (by norm_num) hNpos) hsize
  have hMassSum : ∑ i, (f.tiling.P i).M = f.tiling.S := f.mass_sum
  have hMiPos (i : Fin f.tiling.m) : 0 < (f.tiling.P i).M := by
    have hnon := hExtracted.patch_nonempty i
    rw [← (f.tiling.P i).cardX]
    exact Finset.card_pos.mpr hnon.1
  have hMiCastPos (i : Fin f.tiling.m) : 0 < ((f.tiling.P i).M : ℝ) := by
    exact_mod_cast hMiPos i
  have hMiLeS (i : Fin f.tiling.m) : (f.tiling.P i).M ≤ f.tiling.S := by
    calc
      _ ≤ ∑ j, (f.tiling.P j).M :=
        Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
      _ = f.tiling.S := hMassSum
  let ratio : Fin f.tiling.m → ℝ := fun i =>
    (f.tiling.S : ℝ) / (f.tiling.P i).M
  let ell : Fin f.tiling.m → ℕ := fun i => allocation_roundLength (ratio i)
  let weights : Fin f.tiling.m → ℝ := fun i =>
    (2 : ℝ) ^ (-((ell i : ℕ) : ℤ))
  have hRoundBounds (i : Fin f.tiling.m) :
      (f.tiling.P i).M / f.tiling.S ≤ weights i ∧
        weights i < 2 * (f.tiling.P i).M / f.tiling.S := by
    have hratioPos : 0 < ratio i := div_pos hSpos (hMiCastPos i)
    have hratioOne : 1 ≤ ratio i := by
      apply (le_div_iff₀ (hMiCastPos i)).2
      have hMiLeSReal : ((f.tiling.P i).M : ℝ) ≤ (f.tiling.S : ℝ) := by
        exact_mod_cast hMiLeS i
      nlinarith [hMiLeSReal]
    have h := allocation_dyadicRoundLength_bounds (ratio i) hratioOne
    have hinv : (ratio i)⁻¹ = (f.tiling.P i).M / f.tiling.S := by
      dsimp [ratio]
      field_simp [ne_of_gt hSpos, ne_of_gt (hMiCastPos i)]
    constructor
    · simpa [weights, ell, hinv] using h.1
    · have h' : weights i < 2 * ((f.tiling.P i).M / (f.tiling.S : ℝ)) := by
        simpa [weights, ell, hinv] using h.2
      have hAlg : 2 * ((f.tiling.P i).M / (f.tiling.S : ℝ)) =
          2 * (f.tiling.P i).M / (f.tiling.S : ℝ) := by ring
      rw [← hAlg]
      exact h'
  have hMassSumReal : ∑ i, ((f.tiling.P i).M : ℝ) = (f.tiling.S : ℝ) := by
    exact_mod_cast hMassSum
  have hNormalizedMass : ∑ i, (f.tiling.P i).M / (f.tiling.S : ℝ) = 1 := by
    change (∑ i, ((f.tiling.P i).M : ℝ) / (f.tiling.S : ℝ)) = 1
    rw [← Finset.sum_div, hMassSumReal, div_self hSpos.ne']
  have hKraftLower : 1 ≤ ∑ i, weights i := by
    calc
      _ = ∑ i, (f.tiling.P i).M / (f.tiling.S : ℝ) := hNormalizedMass.symm
      _ ≤ ∑ i, weights i := Finset.sum_le_sum fun i hi => (hRoundBounds i).1
  let rel : Fin f.tiling.m → Fin f.tiling.m → Prop := fun i j => ell i ≤ ell j
  let order := List.insertionSort rel (List.finRange f.tiling.m)
  have hSorted : order.Pairwise rel := List.pairwise_insertionSort rel _
  have hPerm : order.Perm (List.finRange f.tiling.m) :=
    List.perm_insertionSort rel _
  have hOrderSum : (order.map weights).sum = ∑ i, weights i := by
    calc
      _ = ((List.finRange f.tiling.m).map weights).sum := (hPerm.map weights).sum_eq
      _ = ∑ i, weights i := (Fin.sum_univ_def weights).symm
  obtain ⟨pre, a, tail, hOrderDecomp, hPreLt, hCross⟩ :=
    allocation_exists_prefix_cross weights 1 (by norm_num) order (by
      rw [hOrderSum]
      exact hKraftLower)
  have hSortedPrefix : (pre ++ a :: tail).Pairwise rel := by
    simpa [hOrderDecomp] using hSorted
  have hCrossRel := (List.pairwise_append.mp hSortedPrefix).2.2
  have hEllLe (i : Fin f.tiling.m) (hi : i ∈ pre) : ell i ≤ ell a :=
    hCrossRel i hi a (by simp)
  let coeff : Fin f.tiling.m → ℕ := fun i => 2 ^ (ell a - ell i)
  have hWeightFactor (i : Fin f.tiling.m) (hi : i ∈ pre) :
      weights i = (coeff i : ℝ) * weights a := by
    have hlen : ell i ≤ ell a := hEllLe i hi
    have hexp : -(ell i : ℤ) = (↑(ell a - ell i : ℕ) : ℤ) + -(ell a : ℤ) := by
      rw [Nat.cast_sub hlen]
      omega
    calc
      _ = (2 : ℝ) ^ (-(ell i : ℤ)) := rfl
      _ = (2 : ℝ) ^ ((↑(ell a - ell i : ℕ) : ℤ) + -(ell a : ℤ)) := by rw [hexp]
      _ = (2 : ℝ) ^ (↑(ell a - ell i : ℕ) : ℤ) *
          (2 : ℝ) ^ (-(ell a : ℤ)) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = (coeff i : ℝ) * weights a := by
        simp [coeff, weights, zpow_natCast]
  have hPreMultiple : (pre.map weights).sum =
      ((pre.map fun i => (coeff i : ℝ)).sum) * weights a := by
    have hFactors (l : List (Fin f.tiling.m))
        (hfactor : ∀ i ∈ l, weights i = (coeff i : ℝ) * weights a) :
        (l.map weights).sum = ((l.map fun i => (coeff i : ℝ)).sum) * weights a := by
      induction l with
      | nil => simp
      | cons i l ih =>
          have hi := hfactor i (by simp)
          have htail : ∀ j ∈ l, weights j = (coeff j : ℝ) * weights a := by
            intro j hj
            exact hfactor j (by simp [hj])
          simp only [List.map_cons, List.sum_cons]
          rw [hi, ih htail]
          ring
    exact hFactors pre (fun i hi => hWeightFactor i hi)
  have hNegWeight : weights a = ((2 : ℝ) ^ ell a)⁻¹ := by
    simp [weights, zpow_neg, zpow_natCast]
  have hTargetMultiple : (1 : ℝ) = (2 : ℝ) ^ ell a * weights a := by
    rw [hNegWeight]
    exact (mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ ell a ≠ 0)).symm
  have hWeightPos : 0 < weights a := by
    dsimp [weights]
    positivity
  have hCoeffCastSum := allocation_list_natCast_sum coeff pre
  have hCoeffLt : (pre.map fun i => coeff i).sum < 2 ^ ell a := by
    have h := hPreLt
    rw [hPreMultiple, hTargetMultiple] at h
    have hReal := (mul_lt_mul_iff_of_pos_right hWeightPos).mp h
    have hCast : ((pre.map fun i => coeff i).sum : ℝ) <
        ((2 ^ ell a : ℕ) : ℝ) := by
      simpa [hCoeffCastSum] using hReal
    exact_mod_cast hCast
  have hCoeffLe : 2 ^ ell a ≤ (pre.map fun i => coeff i).sum + 1 := by
    have h := hCross
    rw [hPreMultiple, hTargetMultiple] at h
    have hmul : (2 : ℝ) ^ ell a * weights a ≤
        ((pre.map fun i => (coeff i : ℝ)).sum + 1) * weights a := by
      calc
        _ ≤ ((pre.map fun i => (coeff i : ℝ)).sum) * weights a + weights a := h
        _ = _ := by ring
    have hReal := (mul_le_mul_iff_of_pos_right hWeightPos).mp hmul
    have hCast : ((2 ^ ell a : ℕ) : ℝ) ≤
        (((pre.map fun i => coeff i).sum + 1 : ℕ) : ℝ) := by
      simpa [hCoeffCastSum] using hReal
    exact_mod_cast hCast
  have hCoeffEq : (pre.map fun i => coeff i).sum + 1 = 2 ^ ell a := by omega
  have hPrefixExact : (pre.map weights).sum + weights a = 1 := by
    calc
      _ = ((pre.map fun i => (coeff i : ℝ)).sum + 1) * weights a := by
        rw [hPreMultiple]
        push_cast
        ring
      _ = (2 : ℝ) ^ ell a * weights a := by
        have hCoeffEqReal :
            ((pre.map fun i => (coeff i : ℝ)).sum + 1) = (2 : ℝ) ^ ell a := by
          have hCoeffEqCast :
              (((pre.map fun i => coeff i).sum + 1 : ℕ) : ℝ) =
                ((2 ^ ell a : ℕ) : ℝ) := by exact_mod_cast hCoeffEq
          simpa [hCoeffCastSum] using hCoeffEqCast
        rw [hCoeffEqReal]
      _ = 1 := hTargetMultiple.symm
  have hOrderPerm : order.Perm (List.finRange f.tiling.m) := hPerm
  have hOrderNodup : order.Nodup := hOrderPerm.nodup_iff.mpr (List.nodup_finRange _)
  have hPrefixSublist : List.Sublist (pre ++ [a]) order := by
    rw [hOrderDecomp]
    exact List.Sublist.append (List.Sublist.refl pre)
      (List.singleton_sublist.2 (by simp))
  have hPrefixNodup : (pre ++ [a]).Nodup := hOrderNodup.sublist hPrefixSublist
  let A : Finset (Fin f.tiling.m) := (pre ++ [a]).toFinset
  have hAweights : ∑ i ∈ A, weights i = 1 := by
    calc
      _ = ((pre ++ [a]).map weights).sum := by
        simpa [A] using allocation_list_sum_toFinset weights (pre ++ [a]) hPrefixNodup
      _ = (pre.map weights).sum + weights a := by simp [List.map_append, List.sum_append]
      _ = 1 := hPrefixExact
  have hAmem : a ∈ A := by simp [A]
  have hAnonempty : A.Nonempty := ⟨a, hAmem⟩
  have hSelectedMass : (f.tiling.S : ℝ) / 2 < ∑ i ∈ A, (f.tiling.P i).M := by
    have hRoundTerm (i : Fin f.tiling.m) :
        weights i < 2 * ((f.tiling.P i).M / (f.tiling.S : ℝ)) := by
      calc
        _ < 2 * (f.tiling.P i).M / (f.tiling.S : ℝ) := (hRoundBounds i).2
        _ = 2 * ((f.tiling.P i).M / (f.tiling.S : ℝ)) := by ring
    have hRoundTerms : (∑ i ∈ A, weights i) <
        ∑ i ∈ A, 2 * ((f.tiling.P i).M / (f.tiling.S : ℝ)) :=
      Finset.sum_lt_sum_of_nonempty hAnonempty (fun i hi => hRoundTerm i)
    have hRoundSum : (∑ i ∈ A, weights i) <
        2 * (∑ i ∈ A, (f.tiling.P i).M / (f.tiling.S : ℝ)) := by
      rw [Finset.mul_sum]
      exact hRoundTerms
    rw [hAweights] at hRoundSum
    have hSumDiv : (∑ i ∈ A, (f.tiling.P i).M / (f.tiling.S : ℝ)) =
        (∑ i ∈ A, ((f.tiling.P i).M : ℝ)) / (f.tiling.S : ℝ) := by
      rw [Finset.sum_div]
    rw [hSumDiv] at hRoundSum
    have htotal : (f.tiling.S : ℝ) < 2 * (∑ i ∈ A, ((f.tiling.P i).M : ℝ)) := by
      have hratio : (1 : ℝ) <
          (2 * (∑ i ∈ A, ((f.tiling.P i).M : ℝ))) / (f.tiling.S : ℝ) := by
        convert hRoundSum using 1 <;> ring
      simpa using (lt_div_iff₀ hSpos).mp hratio
    have hsumCastA :
        ((∑ i ∈ A, (f.tiling.P i).M : ℕ) : ℝ) =
          ∑ i ∈ A, ((f.tiling.P i).M : ℝ) := by simp
    have htotalNat : (f.tiling.S : ℝ) <
        2 * ((∑ i ∈ A, (f.tiling.P i).M : ℕ) : ℝ) := by
      rw [hsumCastA]
      exact htotal
    exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      (by simpa [mul_comm] using htotalNat)
  let eA : {i : Fin f.tiling.m // i ∈ A} ≃ Fin A.card :=
    Fintype.equivFinOfCardEq (by simp)
  let idx : Fin A.card → Fin f.tiling.m := fun i => (eA.symm i).val
  have hIdxInj : Function.Injective idx := by
    intro i j hij
    apply eA.symm.injective
    exact Subtype.ext hij
  have hIdxNe (i j : Fin A.card) (hij : i ≠ j) : idx i ≠ idx j := by
    intro h
    exact hij (hIdxInj h)
  let Pnew : Fin A.card → Patch (T.orient f.orientation) k := fun i =>
    {f.tiling.P (idx i) with ℓ := ell (idx i)}
  let Tnew : Tiling κ (T.orient f.orientation) k :=
    {f.tiling with
      m := A.card
      P := Pnew
      w := fun i => f.tiling.w (idx i)
      Q := fun i => f.tiling.Q (idx i)}
  have hExtractedNew : ExtractionData Tnew := by
    refine {
      reserveX_card := hExtracted.reserveX_card
      reserveY_card := hExtracted.reserveY_card
      reserveX_subset := hExtracted.reserveX_subset
      reserveY_subset := hExtracted.reserveY_subset
      patch_supports := ?_
      patch_nonempty := ?_
      bins_card := ?_
      patch_X_disjoint := ?_
      patch_Y_disjoint := ?_
      S_upper := hExtracted.S_upper
      measured_scales := ?_
      bounded_scale_cutoff := ?_
      bounded_data := ?_
      direct_scale_bound := ?_
      direct_data := ?_
      cluster_data := ?_
      clique_scales := ?_ }
    · intro i
      simpa [Tnew, Pnew] using hExtracted.patch_supports (idx i)
    · intro i
      simpa [Tnew, Pnew] using hExtracted.patch_nonempty (idx i)
    · intro i B hB
      simpa [Tnew, Pnew] using hExtracted.bins_card (idx i) B hB
    · intro i j hij
      have hidxne := hIdxNe i j hij
      simpa [Tnew, Pnew] using hExtracted.patch_X_disjoint (idx i) (idx j) hidxne
    · intro i j hij
      have hidxne := hIdxNe i j hij
      simpa [Tnew, Pnew] using hExtracted.patch_Y_disjoint (idx i) (idx j) hidxne
    · intro i
      simpa [Tnew, Pnew, idx] using hExtracted.measured_scales (idx i)
    · intro hmode i
      simpa [Tnew, Pnew] using hExtracted.bounded_scale_cutoff hmode (idx i)
    · intro hmode
      rcases hExtracted.bounded_data hmode with ⟨hm, hbd⟩
      have hAcardLe : A.card ≤ 1 := by simpa [hm] using (Finset.card_le_univ A)
      have hAcardPos : 0 < A.card := Finset.card_pos.mpr hAnonempty
      have hAcardOne : A.card = 1 := by omega
      refine ⟨hAcardOne, ?_⟩
      intro i
      rcases hbd (idx i) with ⟨hℓ, hh, hdPatch, hM, hQ⟩
      have hOnly (j : Fin f.tiling.m) : j = idx i := by
        apply Fin.ext
        have hj := j.isLt
        have hi := (idx i).isLt
        omega
      have hMassIdx : (f.tiling.P (idx i)).M = f.tiling.S := by
        rw [← hMassSum]
        symm
        exact Finset.sum_eq_single (idx i)
          (fun j _ hj => (hj (hOnly j)).elim) (by simp)
      have hRatioOne : ratio (idx i) = 1 := by
        dsimp [ratio]
        rw [hMassIdx]
        exact div_self hSpos.ne'
      have hLenZero : ell (idx i) = 0 := by
        simp [ell, allocation_roundLength, hRatioOne, Real.log_one]
      exact ⟨hLenZero, hh, hdPatch, hM, hQ⟩
    · intro hmode i
      simpa [Tnew, Pnew, idx] using hExtracted.direct_scale_bound hmode (idx i)
    · intro hmode i
      simpa [Tnew, Pnew, idx] using hExtracted.direct_data hmode (idx i)
    · intro hmode i
      simpa [Tnew, Pnew, idx] using hExtracted.cluster_data hmode (idx i)
    · intro i
      simpa [Tnew, Pnew, idx, Tiling.kScale] using hExtracted.clique_scales (idx i)
  have hSLower : (1 / 400 : ℝ) * T.S.N k ≤ f.tiling.S := by
    rcases hSelected with ⟨_, hsize⟩ | ⟨_, hsize⟩
    · exact hsize
    · calc
        _ ≤ (1 / 200 : ℝ) * T.S.N k := by nlinarith
        _ ≤ f.tiling.S := hsize
  let R : RoundedFamily κ T k := {
    orientation := f.orientation
    tiling := Tnew
    extracted := hExtractedNew
    S_lower := hSLower
    S_upper := by
      have hN : (T.orient f.orientation).S.N k = T.S.N k := by
        cases f.orientation <;> rfl
      simpa [Tnew, hN] using hExtracted.S_upper
    selected_mass := by
      have hsum : (∑ i : Fin A.card, (Pnew i).M) = ∑ i ∈ A, (f.tiling.P i).M := by
        calc
          _ = ∑ z : {i : Fin f.tiling.m // i ∈ A}, (f.tiling.P z.val).M := by
            exact Fintype.sum_equiv eA.symm _ _ (fun i => rfl)
          _ = ∑ i ∈ A, (f.tiling.P i).M := by
            exact Finset.sum_coe_sort (f := fun i => (f.tiling.P i).M) (s := A)
      change (f.tiling.S : ℝ) / 2 < ((∑ i : Fin A.card, (Pnew i).M : ℕ) : ℝ)
      rw [hsum]
      exact hSelectedMass
    dyadic_mass_lower := by
      intro i
      simpa [Tnew, Pnew, weights] using (hRoundBounds (idx i)).1
    dyadic_mass_upper := by
      intro i
      simpa [Tnew, Pnew, weights] using (hRoundBounds (idx i)).2
    dyadic_sum := by
      calc
        _ = ∑ z : {i : Fin f.tiling.m // i ∈ A}, weights z.val := by
          exact Fintype.sum_equiv eA.symm _ _ (fun i => rfl)
        _ = ∑ i ∈ A, weights i := by
          exact Finset.sum_coe_sort (f := weights) (s := A)
        _ = 1 := hAweights }
  refine ⟨R, ⟨?_⟩⟩
  refine {
    orientation := rfl
    mode := rfl
    colour := rfl
    mass := rfl
    reserveX := HEq.rfl
    reserveY := HEq.rfl
    index := idx
    injective := hIdxInj
    patches := ?_
    clique_scales := ?_ }

  · intro i
    dsimp [R, Tnew, Pnew]
    cases f.tiling.P (idx i)
    rfl
  · intro i
    rfl

/-- P13.3g (sections/13, lines 170–182): Kraft's equality gives a complete prefix code. -/
theorem kraft_prefix_code (κ : CConsts) (T : Stage) (k : ℕ)
    (R : RoundedFamily κ T k)
    (hLength : ∀ i, (R.tiling.P i).ℓ ≤ (T.orient R.orientation).S.n k) :
    ∃ w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k),
      PrefixCodeComplete R w := by
  exact Lane_sol_s13_allocB.complete_prefix_of_kraft
    (fun i => (R.tiling.P i).ℓ) hLength R.dyadic_sum

private theorem allocation_prefixLeaf_card {n ell : ℕ} (w : CubePos n) (hell : ell < n) :
    Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w} = 2 ^ (n - ell) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun j => j.val < ell
  let e : Fin ell ↪ Fin n := {
    toFun := fun j => ⟨j.val, j.isLt.trans hell⟩
    inj' := by
      intro a b hab
      have hv := congrArg (fun x : Fin n => x.val) hab
      change a.val = b.val at hv
      exact Fin.ext hv
  }
  have hS_eq : S = Finset.univ.map e := by
    ext j
    constructor
    · intro hj
      have hj' := (Finset.mem_filter.mp hj).2
      refine Finset.mem_map.mpr ⟨⟨j.val, hj'⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext rfl
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨j', hj', hEq⟩
      subst j
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j'.isLt⟩
  have hScard : S.card = ell := by
    rw [hS_eq]
    simp
  let choices : Fin n → Finset Bool := fun j =>
    if j ∈ S then {w j} else Finset.univ
  let Q := Fintype.piFinset choices
  have hpred (v : CubePos n) : v ∈ prefixLeaf ell w ↔ v ∈ Q := by
    change (∀ j : Fin n, j.val < ell → v j = w j) ↔ v ∈ Q
    constructor
    · intro hv
      apply Fintype.mem_piFinset.mpr
      intro j
      by_cases hj : j ∈ S
      · have hfix := hv j (Finset.mem_filter.mp hj).2
        simp [Q, choices, hj, hfix]
      · simp [Q, choices, hj]
    · intro hv j hj
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      have hmem := Fintype.mem_piFinset.mp hv j
      simpa [Q, choices, hjS] using hmem
  have hF : Finset.univ.filter (fun v : CubePos n => v ∈ prefixLeaf ell w) = Q := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpred v
  have hsub := Fintype.card_congr ((Equiv.refl (CubePos n)).subtypeEquiv hpred)
  calc
    Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w} =
        Fintype.card {v : CubePos n // v ∈ Q} := hsub
    _ = Q.card := Fintype.card_coe Q
    _ = 2 ^ (n - ell) := by
      change (Fintype.piFinset choices).card = _
      rw [Fintype.card_piFinset]
      have hchoice : ∀ j : Fin n, (choices j).card = if j ∈ S then 1 else 2 := by
        intro j
        by_cases hj : j ∈ S <;> simp [choices, hj]
      simp_rw [hchoice]
      rw [Finset.prod_ite]
      have hfilter : Finset.univ.filter (fun j : Fin n => j ∉ S) = Finset.univ \ S := by
        ext j
        simp
      rw [hfilter, Finset.prod_const_one, Finset.prod_const (b := 2),
        Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      simp [hScard]

private theorem allocation_prefixLeaf_even_card {n ell : ℕ} (w : CubePos n) (hell : ell < n) :
    Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w ∧ IsEvenRole v} =
      2 ^ (n - ell - 1) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun j => j.val < ell
  let e : Fin ell ↪ Fin n := {
    toFun := fun j => ⟨j.val, j.isLt.trans hell⟩
    inj' := by
      intro a b hab
      have hv := congrArg (fun x : Fin n => x.val) hab
      change a.val = b.val at hv
      exact Fin.ext hv
  }
  have hS_eq : S = Finset.univ.map e := by
    ext j
    constructor
    · intro hj
      have hj' := (Finset.mem_filter.mp hj).2
      refine Finset.mem_map.mpr ⟨⟨j.val, hj'⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext rfl
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨j', hj', hEq⟩
      subst j
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j'.isLt⟩
  have hScard : S.card = ell := by rw [hS_eq]; simp
  let z : ∀ j : S, Bool := fun j => w j.1
  have hprefix (v : CubePos n) :
      (∀ j : S, v j.1 = z j) ↔ v ∈ prefixLeaf ell w := by
    constructor
    · intro hz
      change ∀ j : Fin n, j.val < ell → v j = w j
      intro j hj
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      simpa [z] using hz ⟨j, hjS⟩
    · intro hv
      change ∀ j : Fin n, j.val < ell → v j = w j at hv
      intro j
      exact hv j (Finset.mem_filter.mp j.property).2
  have hSlt : S.card < n := by simpa [hScard] using hell
  have hParity := parity_projection_uniform S hSlt z
  have hfilter :
      Finset.univ.filter (fun v : CubePos n => v ∈ prefixLeaf ell w ∧ IsEvenRole v) =
        (evenRoleSet n).filter (fun v => ∀ j : S, v j.1 = z j) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, evenRoleSet]
    constructor
    · rintro ⟨hp, he⟩
      exact ⟨he, (hprefix v).mpr hp⟩
    · rintro ⟨he, hz⟩
      exact ⟨(hprefix v).mp hz, he⟩
  have hcard :
      Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w ∧ IsEvenRole v} =
        ((evenRoleSet n).filter (fun v => ∀ j : S, v j.1 = z j)).card := by
    rw [Fintype.card_subtype]
    simpa using congrArg Finset.card hfilter
  calc
    _ = ((evenRoleSet n).filter (fun v => ∀ j : S, v j.1 = z j)).card := hcard
    _ = 2 ^ (n - S.card - 1) := hParity
    _ = 2 ^ (n - ell - 1) := by rw [hScard]

private theorem allocation_prefixLeaf_odd_card {n ell : ℕ} (w : CubePos n) (hell : ell < n) :
    Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w ∧ ¬ IsEvenRole v} =
      2 ^ (n - ell - 1) := by
  classical
  let P : CubePos n → Prop := fun v => v ∈ prefixLeaf ell w
  have hsplit :
      Fintype.card {v : CubePos n // P v ∧ IsEvenRole v} +
        Fintype.card {v : CubePos n // P v ∧ ¬ IsEvenRole v} =
          Fintype.card {v : CubePos n // P v} := by
    have h := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter P) IsEvenRole
    simpa [P, Fintype.card_subtype, Finset.filter_filter, and_comm] using h
  have hleaf := allocation_prefixLeaf_card w hell
  have heven := allocation_prefixLeaf_even_card w hell
  have hpow : 2 ^ (n - ell) = 2 * 2 ^ (n - ell - 1) := by
    have hsplitExp : n - ell = (n - ell - 1) + 1 := by omega
    calc
      2 ^ (n - ell) = 2 ^ ((n - ell - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (n - ell - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - ell - 1) := by ring
  have hsplit' :
      Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w ∧ IsEvenRole v} +
        Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w ∧ ¬ IsEvenRole v} =
          Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w} := by
    simpa [P] using hsplit
  rw [hleaf, heven, hpow] at hsplit'
  omega

private theorem allocation_prefixCoords_card {n ell : ℕ} (hle : ell ≤ n) :
    (Finset.univ.filter fun j : Fin n => j.val < ell).card = ell := by
  classical
  let e : Fin ell ↪ Fin n := {
    toFun := fun j => ⟨j.val, j.isLt.trans_le hle⟩
    inj' := by
      intro a b hab
      have hv := congrArg (fun x : Fin n => x.val) hab
      change a.val = b.val at hv
      exact Fin.ext hv
  }
  have hset : (Finset.univ.filter fun j : Fin n => j.val < ell) = Finset.univ.map e := by
    ext j
    constructor
    · intro hj
      have hj' := (Finset.mem_filter.mp hj).2
      refine Finset.mem_map.mpr ⟨⟨j.val, hj'⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext rfl
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨j', hj', hEq⟩
      subst j
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j'.isLt⟩
  rw [hset]
  simp

/-- P13.3h (sections/13, lines 184–204): prefix geometry gives role counts and distinct crossing leaves. -/
theorem allocation_geometry (κ : CConsts) (T : Stage) (k : ℕ)
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k))
    (hCode : PrefixCodeComplete R w)
    (hFit : PrefixDimensionFit R) : PrefixGeometry R w := by
  classical
  let n := (T.orient R.orientation).S.n k
  have hEllLe (i : Fin R.tiling.m) :
      (R.tiling.P i).ℓ ≤ Finset.univ.sup fun j : Fin R.tiling.m => (R.tiling.P j).ℓ :=
    Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin R.tiling.m => (R.tiling.P j).ℓ) (Finset.mem_univ i)
  have hHLe (i : Fin R.tiling.m) :
      (R.tiling.P i).h ≤ Finset.univ.sup fun j : Fin R.tiling.m => (R.tiling.P j).h :=
    Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin R.tiling.m => (R.tiling.P j).h) (Finset.mem_univ i)
  have hDim (i : Fin R.tiling.m) : (R.tiling.P i).ℓ + (R.tiling.P i).h ≤ n := by
    have hℓ := hEllLe i
    have hh := hHLe i
    have h := hFit.fit
    omega
  have hNpos : (0 : ℝ) < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hSpos : (0 : ℝ) < (R.tiling.S : ℝ) :=
    lt_of_lt_of_le (by positivity) R.S_lower
  have hSupper : (R.tiling.S : ℝ) ≤ (T.S.N k : ℝ) := by exact_mod_cast R.S_upper
  refine {
    prefix_internal_length := hFit.fit
    leaf_card := ?_
    parity_leaf_card := ?_
    odd_leaf_card := ?_
    role_count_bounds := ?_
    crossing_flips := ?_
    coordinate_partition := ?_
    coordinate_disjoint := ?_
    internal_card := ?_
    internal_nested := ?_ }
  · intro i
    exact allocation_prefixLeaf_card (w i) (hFit.free i)
  · intro i
    exact allocation_prefixLeaf_even_card (w i) (hFit.free i)
  · intro i
    exact allocation_prefixLeaf_odd_card (w i) (hFit.free i)
  · intro i
    constructor
    · have hMnonneg : (0 : ℝ) ≤ (R.tiling.P i).M := by positivity
      have hfrac : (R.tiling.P i).M / (T.S.N k : ℝ) ≤
          (R.tiling.P i).M / (R.tiling.S : ℝ) :=
        div_le_div_of_nonneg_left hMnonneg hSpos hSupper
      have hdyadic : (2 : ℝ) ^ (-((R.tiling.P i).ℓ : ℤ)) =
          ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ := by simp
      have hpow : (2 : ℝ) ^ (n - (R.tiling.P i).ℓ - 1) =
          (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ := by
        have hfree := hFit.free i
        have hℓ : (R.tiling.P i).ℓ ≤ n - 1 := by omega
        calc
          _ = (2 : ℝ) ^ (n - 1 - (R.tiling.P i).ℓ) := by congr 1 <;> omega
          _ = (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ :=
            pow_sub₀ (2 : ℝ) (by norm_num) hℓ
      have hcard :
          (Fintype.card {v : CubePos n //
            v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) ∧ IsEvenRole v} : ℝ) =
            (2 : ℝ) ^ (n - (R.tiling.P i).ℓ - 1) := by
        exact_mod_cast allocation_prefixLeaf_even_card (w i) (hFit.free i)
      have hdyLow : (R.tiling.P i).M / (R.tiling.S : ℝ) ≤
          ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ := by
        simpa only [hdyadic] using R.dyadic_mass_lower i
      rw [hcard]
      calc
        (2 : ℝ) ^ (n - 1) * (R.tiling.P i).M / (T.S.N k : ℝ) =
            (2 : ℝ) ^ (n - 1) * ((R.tiling.P i).M / (T.S.N k : ℝ)) := by ring
        _ ≤ (2 : ℝ) ^ (n - 1) * ((R.tiling.P i).M / (R.tiling.S : ℝ)) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ ≤ (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ :=
          mul_le_mul_of_nonneg_left hdyLow (by positivity)
        _ = (2 : ℝ) ^ (n - (R.tiling.P i).ℓ - 1) := hpow.symm
    · have hMnonneg : (0 : ℝ) ≤ (R.tiling.P i).M := by positivity
      have hquarter : (0 : ℝ) < (1 / 400 : ℝ) * (T.S.N k : ℝ) := by positivity
      have hfrac : (R.tiling.P i).M / (R.tiling.S : ℝ) ≤
          (R.tiling.P i).M / ((1 / 400 : ℝ) * (T.S.N k : ℝ)) :=
        div_le_div_of_nonneg_left hMnonneg hquarter R.S_lower
      have hdyadic : (2 : ℝ) ^ (-((R.tiling.P i).ℓ : ℤ)) =
          ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ := by simp
      have hdyHigh : ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ <
          2 * ((R.tiling.P i).M / (R.tiling.S : ℝ)) := by
        calc
          _ < 2 * (R.tiling.P i).M / (R.tiling.S : ℝ) := by
            simpa only [hdyadic] using R.dyadic_mass_upper i
          _ = 2 * ((R.tiling.P i).M / (R.tiling.S : ℝ)) := by ring
      have hfree := hFit.free i
      have hpow : (2 : ℝ) ^ (n - (R.tiling.P i).ℓ - 1) =
          (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ := by
        have hℓ : (R.tiling.P i).ℓ ≤ n - 1 := by omega
        calc
          _ = (2 : ℝ) ^ (n - 1 - (R.tiling.P i).ℓ) := by congr 1 <;> omega
          _ = (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ :=
            pow_sub₀ (2 : ℝ) (by norm_num) hℓ
      have hcard :
          (Fintype.card {v : CubePos n //
            v ∈ prefixLeaf (R.tiling.P i).ℓ (w i) ∧ IsEvenRole v} : ℝ) =
            (2 : ℝ) ^ (n - (R.tiling.P i).ℓ - 1) := by
        exact_mod_cast allocation_prefixLeaf_even_card (w i) (hFit.free i)
      have hpowSucc : (2 : ℝ) ^ (n - 1) * 2 = (2 : ℝ) ^ n := by
        have hfree := hFit.free i
        have hn : n - 1 + 1 = n := by omega
        calc
          (2 : ℝ) ^ (n - 1) * 2 = (2 : ℝ) ^ ((n - 1) + 1) := by rw [pow_succ]
          _ = (2 : ℝ) ^ n := by rw [hn]
      rw [hcard]
      exact le_of_lt <| calc
        (2 : ℝ) ^ (n - (R.tiling.P i).ℓ - 1) =
            (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ (R.tiling.P i).ℓ)⁻¹ := hpow
        _ < (2 : ℝ) ^ (n - 1) *
            (2 * ((R.tiling.P i).M / (R.tiling.S : ℝ))) :=
          mul_lt_mul_of_pos_left hdyHigh (by positivity)
        _ = (2 : ℝ) ^ n * ((R.tiling.P i).M / (R.tiling.S : ℝ)) := by
          calc
            _ = ((2 : ℝ) ^ (n - 1) * 2) *
                ((R.tiling.P i).M / (R.tiling.S : ℝ)) := by ring
            _ = (2 : ℝ) ^ n * ((R.tiling.P i).M / (R.tiling.S : ℝ)) := by rw [hpowSucc]
        _ ≤ (2 : ℝ) ^ n *
            ((R.tiling.P i).M / ((1 / 400 : ℝ) * (T.S.N k : ℝ))) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = (2 : ℝ) ^ n * (R.tiling.P i).M /
            ((1 / 400 : ℝ) * (T.S.N k : ℝ)) := by ring
  · intro i v hv
    classical
    let hLeaves (x : CubePos n) : ∃ t : Fin R.tiling.m,
        x ∈ prefixLeaf (R.tiling.P t).ℓ (w t) := (hCode x).exists
    let f : {j : Fin n // j.val < (R.tiling.P i).ℓ} → Fin R.tiling.m :=
      fun j => Classical.choose (hLeaves (flipPos v j.1))
    have hf (j : {j : Fin n // j.val < (R.tiling.P i).ℓ}) :
        flipPos v j.1 ∈ prefixLeaf (R.tiling.P (f j)).ℓ (w (f j)) :=
      Classical.choose_spec (hLeaves (flipPos v j.1))
    have hflipNot (j : {j : Fin n // j.val < (R.tiling.P i).ℓ}) :
        flipPos v j.1 ∉ prefixLeaf (R.tiling.P i).ℓ (w i) := by
      intro hmem
      have hvj := hv j.1 j.2
      have hfj := hmem j.1 j.2
      have hnot : v j.1 ≠ w i j.1 := by
        change Function.update v j.1 (!v j.1) j.1 = w i j.1 at hfj
        rw [Function.update_self] at hfj
        exact Bool.not_eq_iff.mp hfj
      exact hnot hvj
    have hnotIndex (j : {j : Fin n // j.val < (R.tiling.P i).ℓ}) : f j ≠ i := by
      intro heq
      apply hflipNot j
      simpa [heq] using hf j
    have hinj : Function.Injective f := by
      intro a b hab
      by_contra hne
      have hcoord : a.1 ≠ b.1 := by
        intro heq
        apply hne
        exact Subtype.ext heq
      let t := f a
      have htargetA : flipPos v a.1 ∈ prefixLeaf (R.tiling.P t).ℓ (w t) := by
        simpa [t] using hf a
      have htargetB : flipPos v b.1 ∈ prefixLeaf (R.tiling.P t).ℓ (w t) := by
        simpa [t, hab] using hf b
      by_cases hshort : (R.tiling.P t).ℓ ≤ a.1.val
      · have horig : v ∈ prefixLeaf (R.tiling.P t).ℓ (w t) := by
          intro q hq
          have hqa : q ≠ a.1 := by
            intro heq
            have := congrArg Fin.val heq
            omega
          have hupdate : Function.update v a.1 (!v a.1) q = v q :=
            Function.update_of_ne hqa _ _
          calc
            v q = Function.update v a.1 (!v a.1) q := hupdate.symm
            _ = w t q := htargetA q hq
        rcases hCode v with ⟨u, hu, huniq⟩
        have htu : t = u := huniq t horig
        have hiu : i = u := huniq i hv
        exact hnotIndex a (by simpa [t] using htu.trans hiu.symm)
      · have hshort' : a.1.val < (R.tiling.P t).ℓ := by omega
        have hTA := htargetA a.1 hshort'
        have hnotA : v a.1 ≠ w t a.1 := by
          change Function.update v a.1 (!v a.1) a.1 = w t a.1 at hTA
          rw [Function.update_self] at hTA
          exact Bool.not_eq_iff.mp hTA
        have hupdate : Function.update v b.1 (!v b.1) a.1 = v a.1 :=
          Function.update_of_ne hcoord _ _
        have hTB := htargetB a.1 hshort'
        change Function.update v b.1 (!v b.1) a.1 = w t a.1 at hTB
        rw [hupdate] at hTB
        have hvalB : v a.1 = w t a.1 := by
          exact hTB
        exact hnotA hvalB
    exact ⟨f, fun j => ⟨hnotIndex j, hf j⟩, hinj⟩
  · intro i
    have hdim := hDim i
    ext j
    simp [Tiling.crossingCoords, Tiling.bulkCoords, Tiling.Icoord, topCoordinates]
    omega
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro j hjC hjB
      simp [Tiling.crossingCoords, Tiling.bulkCoords] at hjC hjB
      omega
    · apply Finset.disjoint_left.mpr
      intro j hjC hjI
      simp [Tiling.crossingCoords, Tiling.Icoord, topCoordinates] at hjC hjI
      have hdi := hDim i
      omega
    · apply Finset.disjoint_left.mpr
      intro j hjB hjI
      simp [Tiling.bulkCoords, Tiling.Icoord, topCoordinates] at hjB hjI
      omega
  · intro i
    change (Finset.univ.filter fun j : Fin n => n - (R.tiling.P i).h ≤ j.val).card =
      (R.tiling.P i).h
    let P : Finset (Fin n) := Finset.univ.filter fun j => j.val < n - (R.tiling.P i).h
    have hPcard : P.card = n - (R.tiling.P i).h :=
      allocation_prefixCoords_card (Nat.sub_le n _)
    have htop :
        Finset.univ.filter (fun j : Fin n => n - (R.tiling.P i).h ≤ j.val) =
          Finset.univ \ P := by
      ext j
      simp [P]
    rw [htop, Finset.card_sdiff_of_subset (Finset.subset_univ P)]
    have hhi : (R.tiling.P i).h ≤ n := by
      have hdi := hDim i
      omega
    simp [P, hPcard]
    omega
  · intro i j hij
    intro x hx
    simp [Tiling.Icoord, topCoordinates] at hx ⊢
    omega

set_option maxHeartbeats 1200000 in
private theorem allocation_cluster_parameters {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} (R : RoundedFamily κ T k) (i : Fin R.tiling.m)
    (hm : R.tiling.mode = .lowCluster ∨ R.tiling.mode = .highSmall ∨ R.tiling.mode = .highLarge) :
    κ.Q0 ≤ (R.tiling.P i).q ∧
      ((R.tiling.P i).q : ℝ) ^ (κ.Mlo : ℝ) ≤ (R.tiling.P i).h ∧
      ((R.tiling.P i).h : ℝ) < 2 * ((R.tiling.P i).q : ℝ) ^ (κ.Mhi : ℝ) := by
  try simp only [Real.rpow_eq_pow]
  have hd := R.extracted.cluster_data hm i
  simp only [Real.rpow_eq_pow] at hd
  have hmax : κ.M1 * κ.Q0 ≤ max ((R.tiling.P i).g : ℝ) ((R.tiling.P i).q : ℝ) := by simpa only [Nat.cast_max] using hd.1
  have hgq : ((R.tiling.P i).g : ℝ) ≤ κ.M1 * (R.tiling.P i).q := hd.2.1
  have hq : κ.Q0 ≤ (R.tiling.P i).q := by
    have hm1 : 1 ≤ κ.M1 := by linarith [hκ.M1_big.1]
    have hq0 : (0 : ℝ) ≤ (R.tiling.P i).q := by positivity
    have hqq : ((R.tiling.P i).q : ℝ) ≤ κ.M1 * (R.tiling.P i).q := by nlinarith
    have hupper := max_le hgq hqq
    have hM1 : 0 < κ.M1 := by linarith [hκ.M1_big.1]
    exact (mul_le_mul_iff_right₀ hM1).mp (hmax.trans hupper)
  have hq1 : (1 : ℝ) ≤ (R.tiling.P i).q :=
    (Lane_sol_s13_allocA.threshold hκ).le.trans hq
  have hM := (Lane_sol_s13_allocA.Mhi_positive hκ).2.2
  have hlo := hd.2.2.2.2.2.2.2.1
  have hhi := hd.2.2.2.2.2.2.2.2.1
  have hlower : ((R.tiling.P i).q : ℝ) ^ (κ.Mlo : ℝ) ≤ (R.tiling.P i).h := by
    apply le_trans ?_ hlo
    apply Real.rpow_le_rpow_of_exponent_le hq1
    split_ifs <;> first | exact le_rfl | exact hM
  have hupper : ((R.tiling.P i).h : ℝ) < 2 * ((R.tiling.P i).q : ℝ) ^ (κ.Mhi : ℝ) := by
    apply hhi.trans_le
    gcongr
    split_ifs <;> first | exact hM | exact le_rfl
  exact ⟨hq, hlower, hupper⟩

set_option maxHeartbeats 1200000 in
/-- P13.3i (sections/13, lines 151–155, 205–215): fixed thresholds fit prefixes and internal dimensions
inside the assigned gain budget. -/
theorem scale_bookkeeping (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hBounds : ResidualScaleBoundFacts κ T) :
    ∀ᶠ k in atTop, ∀ R : RoundedFamily κ T k,
      AllocationBounds R.tiling ∧ ScaleRegimeFacts R.tiling := by
  classical
  have hp := Lane_sol_s13_allocA.parameters hκ
  have haBpos := hκ.aB_rng.1
  have haCpos := hκ.aC_rng.1
  have hMhi := Lane_sol_s13_allocA.Mhi_positive hκ
  let γ : ℝ := κ.ι / (4 * (κ.Mhi : ℝ))
  have hγ : 0 < γ := by
    dsimp [γ]
    exact div_pos hκ.ι_rng.1 (mul_pos (by norm_num) (by exact_mod_cast hMhi.2.1))
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  have hlog : Tendsto (fun k => Real.log (T.S.n k)) atTop atTop := by
    simpa only [Function.comp_def] using Real.tendsto_log_atTop.comp hn
  have hsmall := hn.eventually (Lane_sol_consts_adm.eventually_power_sum (κ.ι / 2) 0 κ.ι 2 0 20 (1 / 2)
    (by linarith [hκ.ι_rng.1]) hκ.ι_rng.1 hκ.ι_rng.1 (by norm_num))
  have hlow := hlog.eventually (Lane_sol_consts_adm.eventually_power_bound (κ.cq * (κ.Mlo : ℝ)) (1 / 10) 2 1
    (by
      have := hκ.cq_rng.2
      have hm : (0 : ℝ) < κ.Mlo := by exact_mod_cast hMhi.1
      have hc := (lt_div_iff₀ (by positivity : 0 < 20 * (κ.Mlo : ℝ))).mp this
      nlinarith) (by norm_num))
  filter_upwards [Lane_sol_s13_allocA.oriented_cluster_bound hBounds hγ, hsmall, hlow,
    Lane_sol_s13_allocA.high_small_estimates hκ T, hn.eventually_ge_atTop 2,
    hlog.eventually_gt_atTop 1] with k hQ hSmall hLow hHighSmall hn2 hLog1
  intro R
  have hnr : (1 : ℝ) ≤ T.S.n k := by linarith
  have hn0 : (0 : ℝ) < T.S.n k := by linarith
  have hNo : (T.orient R.orientation).S.n k = T.S.n k := by cases R.orientation <;> rfl
  have hNO : (T.orient R.orientation).S.N k = T.S.N k := by cases R.orientation <;> rfl
  have hN : 0 < T.S.N k := T.S.N_pos k
  have hS : 0 < R.tiling.S := by
    have hNr : (0 : ℝ) < T.S.N k := by exact_mod_cast hN
    exact_mod_cast (show (0 : ℝ) < R.tiling.S by linarith [R.S_lower])
  have hDim : 2 * (T.S.n k : ℝ) ^ (κ.ι / 2) + 20 < (T.S.n k : ℝ) ^ κ.ι := by
    simp only [zero_mul, add_zero] at hSmall
    have hnp := Real.rpow_pos_of_pos hn0 κ.ι
    linarith
  have hLoss (i : Fin R.tiling.m) (r : ℝ)
      (hm : (1 / 400 : ℝ) * T.S.N k * Real.exp (-r) ≤ (R.tiling.P i).M) :
      ((R.tiling.P i).ℓ : ℝ) ≤ 2 * (r + 10) ∧
        Real.log ((T.S.N k : ℝ) / (R.tiling.P i).M) ≤ r + 10 := by
    have hM : 0 < (R.tiling.P i).M := by
      rw [← (R.tiling.P i).cardX]
      exact Finset.card_pos.mpr (R.extracted.patch_nonempty i).1
    exact Lane_sol_s13_allocA.prefix_loss hN hM hS R.S_upper hm (R.dyadic_mass_lower i)
  have hDirect (hm : R.tiling.mode = .lowDirect ∨ R.tiling.mode = .highDirect) (i : Fin R.tiling.m) :
      (max (R.tiling.P i).h (R.tiling.P i).ℓ : ℝ) < ((T.orient R.orientation).S.n k : ℝ) ^ κ.ι ∧
      (((R.tiling.P i).ℓ : ℝ) ≤ R.tiling.gain i / (1000 * κ.u) ∧
        Real.log (((T.orient R.orientation).S.N k : ℝ) / (R.tiling.P i).M) ≤
          R.tiling.gain i / (1000 * κ.u)) := by
    rcases R.extracted.direct_data hm i with ⟨hmax, hgq, hsize, hdegree, hh, hd, hreg⟩
    have hsize' : (1 / 400 : ℝ) * T.S.N k * Real.exp (-((R.tiling.P i).g : ℝ) ^ κ.aB) ≤
        (R.tiling.P i).M := by simpa [hNO] using hsize
    have hl := hLoss i _ hsize'
    have hg := R.extracted.direct_scale_bound hm i
    rw [hNo] at hg
    have hgp : ((R.tiling.P i).g : ℝ) ^ κ.aB ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) := by
      calc
        _ ≤ ((T.S.n k : ℝ) ^ (κ.ι / 2)) ^ κ.aB := by gcongr
        _ = (T.S.n k : ℝ) ^ ((κ.ι / 2) * κ.aB) := (Real.rpow_mul hn0.le _ _).symm
        _ ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) :=
          Real.rpow_le_rpow_of_exponent_le hnr (by nlinarith [hκ.ι_rng.1, hp.2.2.2.2.1])
    have hel : ((R.tiling.P i).ℓ : ℝ) < (T.S.n k : ℝ) ^ κ.ι := by linarith [hl.1]
    have hqg : ((R.tiling.P i).q : ℝ) ≤ (R.tiling.P i).g := by
      have hq0 : (0 : ℝ) ≤ (R.tiling.P i).q := by positivity
      have hm1 := hκ.M1_big.1
      nlinarith
    have hgmin : κ.M1 * κ.Q0 ≤ (R.tiling.P i).g := by
      rw [Nat.cast_max] at hmax
      simpa [max_eq_left hqg] using hmax
    have hbudget := Lane_sol_s13_allocA.direct_budget hκ hgmin
    have hGain : R.tiling.gain i / (1000 * κ.u) = (R.tiling.P i).g / (10 ^ 6 * κ.u) := by
      have hu0 : (κ.u : ℝ) ≠ 0 := by linarith [hp.2.2.1]
      rcases hm with hm | hm <;> simp only [Tiling.gain, hm] <;>
        field_simp [hu0] <;> ring
    rw [hNo, hh]
    simp only [Nat.cast_zero, max_eq_right (by positivity : (0 : ℝ) ≤ (R.tiling.P i).ℓ)]
    refine ⟨hel, ?_⟩
    rw [hGain, hNO]
    constructor
    · exact hl.1.trans hbudget
    · have hpow0 := Real.rpow_nonneg (show (0 : ℝ) ≤ (R.tiling.P i).g by positivity) κ.aB
      linarith [hl.2]
  have hCluster (hm : R.tiling.mode = .lowCluster ∨ R.tiling.mode = .highSmall ∨ R.tiling.mode = .highLarge)
      (i : Fin R.tiling.m) :
      (max (R.tiling.P i).h (R.tiling.P i).ℓ : ℝ) < ((T.orient R.orientation).S.n k : ℝ) ^ κ.ι ∧
      (((R.tiling.P i).ℓ : ℝ) ≤ R.tiling.gain i / (1000 * κ.u) ∧
        Real.log (((T.orient R.orientation).S.N k : ℝ) / (R.tiling.P i).M) ≤
          R.tiling.gain i / (1000 * κ.u)) := by
    obtain ⟨hqmin, hhlo, hhhi⟩ := allocation_cluster_parameters hκ R i hm
    have hdata := R.extracted.cluster_data hm i
    simp only [Real.rpow_eq_pow] at hdata
    have hsize : (1 / 400 : ℝ) * T.S.N k * Real.exp (-((R.tiling.P i).q : ℝ) ^ κ.aC) ≤
        (R.tiling.P i).M := by simpa [hNO] using hdata.2.2.1
    have hl := hLoss i _ hsize
    have hsupports := R.extracted.patch_supports i
    have hRX := hsupports.2.1.trans Finset.sdiff_subset
    have hRY := hsupports.2.2.2.trans Finset.sdiff_subset
    have hqb := hQ R.orientation (R.tiling.P i).resX (R.tiling.P i).resY hRX hRY
    rw [← (R.extracted.measured_scales i).2] at hqb
    have hq1 : (1 : ℝ) ≤ (R.tiling.P i).q := (Lane_sol_s13_allocA.threshold hκ).le.trans hqmin
    have hMhiReal : (1 : ℝ) ≤ κ.Mhi := by
      have hnat : 1 ≤ κ.Mhi := by have ht := hMhi.2.1; omega
      exact_mod_cast hnat
    have hγM : γ * (κ.Mhi : ℝ) = κ.ι / 4 := by
      dsimp [γ]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hMhi.2.1)]
      <;> ring
    have hPow : ((R.tiling.P i).q : ℝ) ^ (κ.Mhi : ℝ) ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) := by
      calc
        _ ≤ ((T.S.n k : ℝ) ^ γ) ^ (κ.Mhi : ℝ) := by gcongr
        _ = (T.S.n k : ℝ) ^ (γ * (κ.Mhi : ℝ)) := (Real.rpow_mul hn0.le _ _).symm
        _ ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) :=
          Real.rpow_le_rpow_of_exponent_le hnr (by rw [hγM]; linarith [hκ.ι_rng.1])
    have hqp : ((R.tiling.P i).q : ℝ) ^ κ.aC ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) := by
      calc
        _ ≤ ((T.S.n k : ℝ) ^ γ) ^ κ.aC := by gcongr
        _ = (T.S.n k : ℝ) ^ (γ * κ.aC) := (Real.rpow_mul hn0.le _ _).symm
        _ ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) := by
          apply Real.rpow_le_rpow_of_exponent_le hnr
          have hgM : γ * (κ.Mhi : ℝ) = κ.ι / 4 := hγM
          have hmul := mul_le_mul_of_nonneg_left (show κ.aC ≤ (κ.Mhi : ℝ) by linarith [hp.2.2.2.1]) hγ.le
          linarith [hκ.ι_rng.1]
    have hhDim : ((R.tiling.P i).h : ℝ) < (T.S.n k : ℝ) ^ κ.ι := by linarith
    have helDim : ((R.tiling.P i).ℓ : ℝ) < (T.S.n k : ℝ) ^ κ.ι := by linarith [hl.1]
    have hbudget := Lane_sol_s13_allocA.cluster_budget hκ hqmin hhlo
    have hGain : R.tiling.gain i = κ.a * (R.tiling.P i).h / 10 ^ 6 := by
      rcases hm with hm | hm | hm <;> simp [Tiling.gain, hm]
    rw [hNo]
    refine ⟨max_lt hhDim helDim, ?_⟩
    rw [hGain, hNO]
    constructor
    · exact hl.1.trans hbudget
    · have hpow0 := Real.rpow_nonneg (show (0 : ℝ) ≤ (R.tiling.P i).q by positivity) κ.aC
      linarith [hl.2]
  refine ⟨?_, ?_⟩
  · intro i
    cases hm : R.tiling.mode with
    | bounded =>
      have hbd := (R.extracted.bounded_data hm).2 i
      simp only [hbd.1, hbd.2.1, max_self, Nat.cast_zero]
      exact ⟨by rw [hNo]; positivity, Or.inl trivial⟩
    | lowDirect => exact ⟨(hDirect (Or.inl hm) i).1, Or.inr (hDirect (Or.inl hm) i).2⟩
    | highDirect => exact ⟨(hDirect (Or.inr hm) i).1, Or.inr (hDirect (Or.inr hm) i).2⟩
    | lowCluster => exact ⟨(hCluster (Or.inl hm) i).1, Or.inr (hCluster (Or.inl hm) i).2⟩
    | highSmall => exact ⟨(hCluster (Or.inr (Or.inl hm)) i).1, Or.inr (hCluster (Or.inr (Or.inl hm)) i).2⟩
    | highLarge => exact ⟨(hCluster (Or.inr (Or.inr hm)) i).1, Or.inr (hCluster (Or.inr (Or.inr hm)) i).2⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hm
      have hmode : R.tiling.mode = .lowCluster ∨ R.tiling.mode = .highSmall ∨ R.tiling.mode = .highLarge := by
        cases hh : R.tiling.mode with
        | bounded => simp only [hh, Mode.isCluster] at hm
        | lowDirect => simp only [hh, Mode.isCluster] at hm
        | highDirect => simp only [hh, Mode.isCluster] at hm
        | lowCluster => exact Or.inl rfl
        | highSmall => exact Or.inr (Or.inl rfl)
        | highLarge => exact Or.inr (Or.inr rfl)
      obtain ⟨hqmin, hhlo, hhhi⟩ := allocation_cluster_parameters hκ R i hmode
      have hh1 : 1 ≤ (R.tiling.P i).h := by
        have := (Real.one_le_rpow ((Lane_sol_s13_allocA.threshold hκ).le.trans hqmin)
          (by positivity : 0 ≤ (κ.Mlo : ℝ))).trans hhlo
        exact_mod_cast this
      refine ⟨Lane_sol_s13_allocA.cluster_tuple_bound hκ hqmin hhhi hh1, ?_⟩
      have hdata := R.extracted.cluster_data hmode i
      simp only [Real.rpow_eq_pow] at hdata
      by_cases hsmall : R.tiling.mode = .highSmall
      · have hd := hdata.2.2.2.1 hsmall
        have hqL := (hdata.2.2.2.2.2.2.2.2.2.2.1.mp hsmall).2
        rw [hNo] at hqL
        rw [hd]
        simpa only [Tiling.kScale, Tiling.tScale, hNo] using (hHighSmall _ _ hqmin hqL hhlo hhhi).1
      · have hother : R.tiling.mode = .lowCluster ∨ R.tiling.mode = .highLarge := by tauto
        have hd := hdata.2.2.2.2.1 hother
        rw [hd]
        simpa only [Tiling.kScale, Tiling.tScale] using (Lane_sol_s13_allocA.cluster_full_bin hκ hqmin hhlo hhhi).1
    · intro hm i
      have hdata := R.extracted.cluster_data (Or.inl hm) i
      simp only [Real.rpow_eq_pow] at hdata
      have hhhi := hdata.2.2.2.2.2.2.2.2.1
      have hqL := hdata.2.2.2.2.2.2.2.2.2.1.mp hm
      rw [hNo] at hqL
      rw [if_pos hm] at hhhi
      have hq0 : (0 : ℝ) ≤ (R.tiling.P i).q := by positivity
      have hbound : ((R.tiling.P i).h : ℝ) <
          2 * (Real.log (T.S.n k)) ^ (κ.cq * (κ.Mlo : ℝ)) := by
        calc
          _ < 2 * ((R.tiling.P i).q : ℝ) ^ (κ.Mlo : ℝ) := hhhi
          _ ≤ 2 * ((Real.log (T.S.n k)) ^ κ.cq) ^ (κ.Mlo : ℝ) := by gcongr
          _ = 2 * (Real.log (T.S.n k)) ^ (κ.cq * (κ.Mlo : ℝ)) := by
            rw [← Real.rpow_mul (by linarith : 0 ≤ Real.log (T.S.n k))]
      rw [hNo]
      exact hbound.le.trans (by simpa only [one_mul, Real.rpow_eq_pow] using hLow)
    · intro hm i
      have hmode : R.tiling.mode = .lowCluster ∨ R.tiling.mode = .highSmall ∨ R.tiling.mode = .highLarge := by tauto
      have hdata := R.extracted.cluster_data hmode i
      simp only [Real.rpow_eq_pow] at hdata
      have hnotLow : R.tiling.mode ≠ .lowCluster := by rcases hm with hm | hm <;> simp [hm]
      have hqL : (Real.log ((T.orient R.orientation).S.n k)) ^ κ.cq < (R.tiling.P i).q := by
        have he := hdata.2.2.2.2.2.2.2.2.2.1
        exact lt_of_not_ge (fun h => hnotLow (he.mpr h))
      have hhlo := hdata.2.2.2.2.2.2.2.1
      rw [if_neg hnotLow] at hhlo
      rw [hNo] at hqL ⊢
      calc
        (Real.log (T.S.n k)) ^ 5 = (Real.log (T.S.n k)) ^ (5 : ℝ) := by norm_num only [Real.rpow_natCast, Real.rpow_ofNat]
        _ < (Real.log (T.S.n k)) ^ (κ.cq * (κ.Mhi : ℝ)) :=
          Real.rpow_lt_rpow_of_exponent_lt hLog1 hκ.Mhi_big.2
        _ = ((Real.log (T.S.n k)) ^ κ.cq) ^ (κ.Mhi : ℝ) :=
          Real.rpow_mul (by linarith : 0 ≤ Real.log (T.S.n k)) _ _
        _ ≤ ((R.tiling.P i).q : ℝ) ^ (κ.Mhi : ℝ) := by gcongr
        _ ≤ (R.tiling.P i).h := hhlo
    · intro hm i
      obtain ⟨hqmin, hhlo, hhhi⟩ := allocation_cluster_parameters hκ R i (Or.inr (Or.inl hm))
      have hdata := R.extracted.cluster_data (Or.inr (Or.inl hm)) i
      simp only [Real.rpow_eq_pow] at hdata
      have hd := hdata.2.2.2.1 hm
      have hqL := (hdata.2.2.2.2.2.2.2.2.2.2.1.mp hm).2
      rw [hNo] at hqL
      rw [hd]
      simpa only [Real.rpow_eq_pow, hNo] using (hHighSmall _ _ hqmin hqL hhlo hhhi).2

/-- P13.3i→h (sections/13, line 210): uniformly small dimensions fit, with a
free parity coordinate, at all sufficiently large indices. -/
theorem allocation_dimension_fit (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ R : RoundedFamily κ T k,
      AllocationBounds R.tiling → PrefixDimensionFit R := by
  have hιhalf : κ.ι < (1 / 2 : ℝ) := by
    have hmin₁ : min κ.η0 (0.01 : ℝ) ≤ (0.01 : ℝ) := min_le_right _ _
    have hmin₂ : min κ.xs (min κ.η0 (0.01 : ℝ)) ≤ (0.01 : ℝ) :=
      (min_le_right _ _).trans hmin₁
    have hι := hκ.ι_rng.2
    nlinarith
  have hnlarge : ∀ᶠ k in atTop, 4 ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 4
  filter_upwards [hnlarge] with k hk
  intro R hAlloc
  let n := T.S.n k
  have hnreal : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
  have hnbase : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have horient : (T.orient R.orientation).S.n k = n := by
    cases R.orientation <;> rfl
  have hpow : (n : ℝ) ^ κ.ι ≤ (n : ℝ) / 2 := by
    calc
      (n : ℝ) ^ κ.ι ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnbase hιhalf.le
      _ = Real.sqrt (n : ℝ) := by rw [← Real.sqrt_eq_rpow]
      _ ≤ (n : ℝ) / 2 := by
        rw [Real.sqrt_le_left (by positivity)]
        have hprod := mul_nonneg (sub_nonneg.mpr hnreal) (show (0 : ℝ) ≤ n by positivity)
        nlinarith [hprod]
  have hhalf : ∀ i : Fin R.tiling.m,
      (R.tiling.P i).h ≤ n / 2 ∧ (R.tiling.P i).ℓ ≤ n / 2 := by
    intro i
    have hmaxReal : max ((R.tiling.P i).h : ℝ) ((R.tiling.P i).ℓ : ℝ) <
        (n : ℝ) / 2 := by
      calc
        _ < ((T.orient R.orientation).S.n k : ℝ) ^ κ.ι := (hAlloc i).1
        _ = (n : ℝ) ^ κ.ι := by rw [horient]
        _ ≤ (n : ℝ) / 2 := hpow
    have hmaxTwiceRealLt : (2 : ℝ) *
        max ((R.tiling.P i).h : ℝ) ((R.tiling.P i).ℓ : ℝ) < n :=
      (lt_div_iff₀' (by norm_num : (0 : ℝ) < 2)).mp hmaxReal
    have hmaxTwiceReal : (2 : ℝ) *
        max ((R.tiling.P i).h : ℝ) ((R.tiling.P i).ℓ : ℝ) ≤ n := by
      exact hmaxTwiceRealLt.le
    have hhtwiceReal : (2 : ℝ) * (R.tiling.P i).h ≤ n := by
      exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans hmaxTwiceReal
    have heltwiceReal : (2 : ℝ) * (R.tiling.P i).ℓ ≤ n := by
      exact (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)).trans hmaxTwiceReal
    have hhtwice : 2 * (R.tiling.P i).h ≤ n := by exact_mod_cast hhtwiceReal
    have heltwice : 2 * (R.tiling.P i).ℓ ≤ n := by exact_mod_cast heltwiceReal
    exact ⟨by omega, by omega⟩
  have hEllSup : (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).ℓ) ≤ n / 2 := by
    apply Finset.sup_le
    intro i hi
    exact (hhalf i).2
  have hHSup : (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).h) ≤ n / 2 := by
    apply Finset.sup_le
    intro i hi
    exact (hhalf i).1
  have hfree : ∀ i, (R.tiling.P i).ℓ < (T.orient R.orientation).S.n k := by
    intro i
    rw [horient]
    have hi := (hhalf i).2
    omega
  have hfit :
      (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).ℓ) +
        (Finset.univ.sup fun i : Fin R.tiling.m => (R.tiling.P i).h) ≤
          (T.orient R.orientation).S.n k := by
    rw [horient]
    omega
  exact ⟨hfree, hfit⟩

private theorem tiling_valid_of_parts {κ : CConsts} {T : Stage} {k : ℕ}
    (R : RoundedFamily κ T k)
    (w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k))
    (hPrefix : PrefixCodeComplete R w)
    (hGeometry : PrefixGeometry R w)
    (hAlloc : AllocationBounds R.tiling) :
    Tiling.Valid (κ := κ) (withPrefixWords R w).tiling := by
  let Rw := withPrefixWords R w
  let 𝒯 : Tiling κ (T.orient R.orientation) k := Rw.tiling
  have hE : ExtractionData 𝒯 := Rw.extracted
  have hN : (T.orient R.orientation).S.N k = T.S.N k := by
    cases R.orientation <;> rfl
  have hS : (1 / 400 : ℝ) * (T.orient R.orientation).S.N k ≤ 𝒯.S := by
    change (1 / 400 : ℝ) * (T.orient R.orientation).S.N k ≤ R.tiling.S
    simpa [hN] using R.S_lower
  have hSupper : 𝒯.S ≤ (T.orient R.orientation).S.N k := by
    change R.tiling.S ≤ (T.orient R.orientation).S.N k
    simpa [hN] using R.S_upper
  refine {
    reserveX_card := hE.reserveX_card
    reserveY_card := hE.reserveY_card
    reserveX_subset := hE.reserveX_subset
    reserveY_subset := hE.reserveY_subset
    patch_supports := hE.patch_supports
    patch_nonempty := hE.patch_nonempty
    bins_card := hE.bins_card
    patch_X_disjoint := hE.patch_X_disjoint
    patch_Y_disjoint := hE.patch_Y_disjoint
    S_lower := hS
    S_upper := hSupper
    selected_mass := R.selected_mass
    dyadic_mass_lower := R.dyadic_mass_lower
    dyadic_mass_upper := R.dyadic_mass_upper
    dyadic_sum := R.dyadic_sum
    prefix_complete := ?_
    prefix_internal_length := hGeometry.prefix_internal_length
    measured_scales := hE.measured_scales
    bounded_scale_cutoff := hE.bounded_scale_cutoff
    bounded_data := hE.bounded_data
    direct_scale_bound := hE.direct_scale_bound
    direct_data := hE.direct_data
    cluster_data := hE.cluster_data
    allocation_bounds := by
      simpa [𝒯, Rw, withPrefixWords, AllocationBounds, Tiling.gain] using hAlloc
    clique_scales := hE.clique_scales }
  intro v
  change ∃! i, v ∈ prefixLeaf (R.tiling.P i).ℓ (w i)
  exact hPrefix v

/-- P13.3 (sections/13, lines 52–216): allocation with the retained-subfamily
provenance, all role/crossing/internal-coordinate facts, and scale regimes. -/
theorem extraction_allocation_with_facts (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : DeepDisc T κ.xs κ.α 0.04)
    (hDeepι : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hClu : ClusterAbsenceInput κ T) :
    ∀ᶠ k in atTop, ∃ R : RoundedFamily κ T k, ∃ f : PassFamily κ T k,
      Nonempty (RoundingProvenance f R) ∧ Tiling.Valid R.tiling ∧
        PrefixGeometry R R.tiling.w ∧ ScaleRegimeFacts R.tiling := by
  have hSample := random_subset_lemma
  have hScaleSpec := d13_1_residual_scale_specification
  have hScaleBounds := residual_scale_bounds κ hκ T hInit hDeepι hClu
  have hDirect := direct_patch_from_bias κ hκ T hSample.1 hScaleBounds
  have hClusterTrim := clean_cluster_scale_witness κ hκ T hInit
  have hCluster := cluster_patch_from_witness κ hκ T hInit hSample.1 hClusterTrim hScaleBounds
  have hBounded := bounded_patch κ T
  have hPass := extraction_passes κ hκ T hInit hDeep hDeepι hClu
    hSample.1 hDirect hCluster hBounded hScaleSpec hScaleBounds
  have hBook := scale_bookkeeping κ hκ T hScaleBounds
  have hFit := allocation_dimension_fit κ hκ T
  filter_upwards [hPass, hBook, hFit] with k hPool hkBook hkFit
  obtain ⟨pool⟩ := hPool
  obtain ⟨f, hf, hselected⟩ := type_selection κ T k pool.families
    pool.families_mass pool.type_tags_nodup pool.mass_or_bounded
  have hFamilyExtraction := f.extracted
  obtain ⟨R, ⟨hKeep⟩⟩ :=
    dyadic_rounding κ hκ T k f hFamilyExtraction hselected
  have hScaleFacts := hkBook R
  have hDimensions := hkFit R hScaleFacts.1
  obtain ⟨w, hCode⟩ := kraft_prefix_code κ T k R (fun i => (hDimensions.free i).le)
  have hGeom := allocation_geometry κ T k R w hCode hDimensions
  refine ⟨withPrefixWords R w, f, ⟨roundingProvenance_withWords hKeep w⟩, ?_, ?_, ?_⟩
  · exact tiling_valid_of_parts R w hCode hGeom hScaleFacts.1
  · exact ⟨hGeom.prefix_internal_length, hGeom.leaf_card, hGeom.parity_leaf_card,
      hGeom.odd_leaf_card, hGeom.role_count_bounds, hGeom.crossing_flips,
      hGeom.coordinate_partition, hGeom.coordinate_disjoint, hGeom.internal_card,
      hGeom.internal_nested⟩
  · exact hScaleFacts.2

/-- P13.3: the original tiling export, projected from the full allocation assembly. -/
theorem extraction_allocation (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0)
    (hDeep : DeepDisc T κ.xs κ.α 0.04)
    (hDeepι : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hClu : ClusterAbsenceInput κ T) :
    ∀ᶠ k in atTop, ∃ o : Bool, ∃ 𝒯 : Tiling κ (T.orient o) k, Tiling.Valid 𝒯 := by
  filter_upwards [extraction_allocation_with_facts κ hκ T hInit hDeep hDeepι hClu]
    with k hk
  obtain ⟨R, f, hKeep, hValid, hGeometry, hRegime⟩ := hk
  exact ⟨R.orientation, R.tiling, hValid⟩

end HypercubeRamsey.S13
