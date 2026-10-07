import HypercubeRamsey.S13.ResidualBounds
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.Framework.Embedding

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

/-- L13.3a (sections/13, lines 141–147): direct bias extraction from a witness and absence at twice its budget. -/
theorem direct_patch_from_bias (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hSampling : UniformSubsampleStatement)
    (hBounds : ResidualScaleBoundFacts κ T) :
    ∀ᶠ k in atTop, ∀ (RX RY : Finset (Fin (T.S.N k))) (g : ℕ),
      RX ⊆ T.X k → RY ⊆ T.Y k →
      (κ.M1 * κ.Q0 ≤ (g : ℝ)) → BiasWitness κ T k RX RY g →
      ¬ BiasWitness κ T k RX RY (2 * g) → DirectPatchData κ T k RX RY g := by
  sorry

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
  sorry

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
  sorry

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
    

/-- P13.3f (sections/13, lines 170–182): round dyadic masses upward and retain the first complete segment. -/
theorem dyadic_rounding (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (k : ℕ)
    (f : PassFamily κ T k)
    (hExtracted : ExtractionData f.tiling)
    (hSelected : (f.tiling.mode = .bounded ∧ (1 / 400 : ℝ) * T.S.N k ≤ f.tiling.S) ∨
       (f.tiling.mode ≠ .bounded ∧ (1 / 200 : ℝ) * T.S.N k ≤ f.tiling.S)) :
    ∃ R : RoundedFamily κ T k, Nonempty (RoundingProvenance f R) := by
  sorry

/-- P13.3g (sections/13, lines 170–182): Kraft's equality gives a complete prefix code. -/
theorem kraft_prefix_code (κ : CConsts) (T : Stage) (k : ℕ)
    (R : RoundedFamily κ T k)
    (hLength : ∀ i, (R.tiling.P i).ℓ ≤ (T.orient R.orientation).S.n k) :
    ∃ w : Fin R.tiling.m → CubePos ((T.orient R.orientation).S.n k),
      PrefixCodeComplete R w := by
  sorry

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

/-- P13.3i (sections/13, lines 151–155, 205–215): fixed thresholds fit prefixes and internal dimensions
inside the assigned gain budget. -/
theorem scale_bookkeeping (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hBounds : ResidualScaleBoundFacts κ T) :
    ∀ᶠ k in atTop, ∀ R : RoundedFamily κ T k,
      AllocationBounds R.tiling ∧ ScaleRegimeFacts R.tiling := by
  sorry

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
