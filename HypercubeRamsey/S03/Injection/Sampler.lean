import HypercubeRamsey.Framework.FinProb
import HypercubeRamsey.Tools.Concentration

/-!
# Lemma 3.9, the stopped sequential process (TeX 03:649–693)

Indices are zero based: time `b` means that rows `0,…,b-1` have been drawn.
The terminal time `t` is included. `none` is an absorbing failure, so the law
is defined even when a free-label denominator vanishes. All weights below
are concrete; the normalization and analytic estimates are proof nodes.
-/

namespace HypercubeRamsey.Injection

open Filter Classical
open scoped BigOperators

abbrev Path (t d : ℕ) := Fin t → Option (Fin d)

/-- The slack away from full occupancy is needed for all denominator estimates. -/
structure OrderedInput (d t : ℕ) (q : Fin t → Fin d → ℝ) : Prop where
  dimension : 100 ≤ d
  horizon : (t : ℝ) ≤ 3 * (d : ℝ) / 4
  nonneg : ∀ i y, 0 ≤ q i y
  row_sum : ∀ i, ∑ y, q i y = 1
  atom : ∀ i y, q i y ≤ 10 * (d : ℝ) ^ (-(0.95 : ℝ))
  column_prefix : ∀ (b : Fin (t + 1)) y,
    |(∑ k : Fin t, if k.val < b.val then q k y else 0) -
      (b.val : ℝ) / d| ≤ 10 * (d : ℝ) ^ (-(1 / 8 : ℝ))

noncomputable def usedMass {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (a : Fin t) (b : ℕ) : ℝ :=
  ∑ k : Fin t, if k.val < b then (x k).elim 0 (q a) else 0

/-- Finite maximum, including zero so it is defined for no rows. -/
noncomputable def trackingError {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (b : ℕ) : ℝ :=
  sSup ({0} ∪ {r | ∃ a : Fin t, ∃ k : Fin (t + 1),
    k.val ≤ b ∧ r = |usedMass q x a k.val - (k.val : ℝ) / d|})

def PrefixValid {d t : ℕ} (x : Path t d) (b : ℕ) : Prop :=
  (∀ k : Fin t, k.val < b → ∃ y, x k = some y) ∧
  (∀ i j : Fin t, i.val < b → j.val < b → x i = x j → i = j)

def Free {d t : ℕ} (x : Path t d) (b : ℕ) (y : Fin d) : Prop :=
  ∀ k : Fin t, k.val < b → x k ≠ some y

private def prefixOf {α : Type*} {n : ℕ} (x : Fin n → α) (j : Fin n) : Fin j → α :=
  fun i => x ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩

private def snocPath {α : Type*} {n : ℕ} (p : Fin n → α) (z : α) : Fin (n + 1) → α :=
  fun i => if hi : i.val < n then p ⟨i.val, hi⟩ else z

/-- A product of kernels whose `j`th factor sees only the prefix before `j` has total mass one. -/
private theorem triangularKernelSum {α : Type*} [Fintype α] [Nonempty α] (n : ℕ)
    (K : ∀ j : Fin n, (Fin j → α) → α → ℝ)
    (hnorm : ∀ j p, ∑ z, K j p z = 1) :
    ∑ x : Fin n → α, ∏ j, K j (prefixOf x j) (x j) = 1 := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      let K' : ∀ j : Fin n, (Fin j → α) → α → ℝ := fun j p z => K j.castSucc p z
      have hK' : ∀ j p, ∑ z, K' j p z = 1 := by
        intro j p
        exact hnorm j.castSucc p
      have hind := ih K' hK'
      let e : (Fin n → α) × α ≃ (Fin (n + 1) → α) :=
        (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ : Fin (n + 1) => α))
      have heS (p : Fin n → α) (z : α) :
          e (p, z) = (@Fin.snoc n (fun _ : Fin (n + 1) => α) p z) := by
        rfl
      have he (p : Fin n → α) (z : α) : e (p, z) = snocPath p z := by
        funext i
        by_cases hi : i.val < n
        · have hs : (@Fin.snoc n (fun _ : Fin (n + 1) => α) p z) i =
              p (Fin.castLT i hi) := by
            have hs' := @Fin.snoc_castSucc n (fun _ : Fin (n + 1) => α) z p (Fin.castLT i hi)
            rw [Fin.castSucc_castLT i hi] at hs'
            exact hs'
          calc
            e (p, z) i = (@Fin.snoc n (fun _ : Fin (n + 1) => α) p z) i :=
              congrFun (heS p z) i
            _ = p (Fin.castLT i hi) := hs
            _ = p ⟨i.val, hi⟩ := by exact congrArg p (Fin.ext rfl)
            _ = snocPath p z i := by simp [snocPath, hi]
        · have hlast : i = Fin.last n := Fin.eq_last_of_not_lt hi
          subst i
          calc
            e (p, z) (Fin.last n) =
                (@Fin.snoc n (fun _ : Fin (n + 1) => α) p z) (Fin.last n) := congrFun (heS p z) _
            _ = z := by simp [Fin.snoc]
            _ = snocPath p z (Fin.last n) := by simp [snocPath]
      have hsum :
          (∑ x : Fin (n + 1) → α, ∏ j, K j (prefixOf x j) (x j)) =
            ∑ p : Fin n → α, ∑ z : α,
              ∏ j, K j (prefixOf (snocPath p z) j) ((snocPath p z) j) := by
        calc
          _ = ∑ w : (Fin n → α) × α,
                ∏ j, K j (prefixOf (e w) j) ((e w) j) :=
              (Equiv.sum_comp e (fun x => ∏ j, K j (prefixOf x j) (x j))).symm
          _ = ∑ p : Fin n → α, ∑ z : α,
                ∏ j, K j (prefixOf (snocPath p z) j) ((snocPath p z) j) := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro p hp
              apply Finset.sum_congr rfl
              intro z hz
              rw [he]
      rw [hsum]
      have hdecomp (p : Fin n → α) (z : α) :
          (∏ j : Fin (n + 1), K j (prefixOf (snocPath p z) j) (snocPath p z j)) =
            (∏ j : Fin n, K' j (prefixOf p j) (p j)) * K (Fin.last n) p z := by
        rw [Fin.prod_univ_castSucc]
        congr 1
        · apply Finset.prod_congr rfl
          intro j hj
          have hcur : snocPath p z j.castSucc = p j := by simp [snocPath]
          have hpre : prefixOf (snocPath p z) j.castSucc = prefixOf p j := by
            funext i
            have hi : i.val < n := lt_trans i.isLt j.isLt
            simp [prefixOf, snocPath, hi]
          rw [hpre, hcur]
        · have hpre : prefixOf (snocPath p z) (Fin.last n) = p := by
            funext i
            simp [prefixOf, snocPath]
          rw [hpre]
          simp [snocPath]
      have houter (p : Fin n → α) :
          (∑ z : α, ∏ j : Fin (n + 1),
            K j (prefixOf (snocPath p z) j) (snocPath p z j)) =
            (∏ j : Fin n, K' j (prefixOf p j) (p j)) *
              (∑ z : α, K (Fin.last n) p z) := by
        calc
          _ = ∑ z : α,
              (∏ j : Fin n, K' j (prefixOf p j) (p j)) * K (Fin.last n) p z := by
            apply Finset.sum_congr rfl
            intro z hz
            exact hdecomp p z
          _ = _ := by rw [Finset.mul_sum]
      calc
        _ = ∑ p : Fin n → α,
              (∏ j : Fin n, K' j (prefixOf p j) (p j)) *
                (∑ z : α, K (Fin.last n) p z) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact houter p
      _ = ∑ p : Fin n → α, ∏ j : Fin n, K' j (prefixOf p j) (p j) := by
          simp [hnorm]
      _ = 1 := hind

noncomputable def availableMass {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (j : Fin t) (B : Finset (Fin d)) : ℝ :=
  ∑ y, if Free x j.val y ∧ y ∉ B then q j y else 0

/-- Draw the row law restricted to free, unreserved labels; fail on a stop
or an empty allowed support. -/
noncomputable def ordinaryWeight {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (j : Fin t) (B : Finset (Fin d)) (z : Option (Fin d)) : ℝ :=
  if PrefixValid x j.val ∧ trackingError q x j.val ≤ 1 / 20 ∧
      0 < availableMass q x j B then
    match z with
    | none => 0
    | some y => if Free x j.val y ∧ y ∉ B then
        q j y / availableMass q x j B else 0
  else if z = none then 1 else 0

noncomputable def sequentialWeight {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) : ℝ := ∏ j, ordinaryWeight q x j ∅ (x j)

private def pathOfPrefix {d t : ℕ} (j : Fin t)
    (p : Fin j → Option (Fin d)) : Path t d :=
  fun k => if hk : k.val < j.val then p ⟨k.val, hk⟩ else none

private theorem usedMass_eq_of_prefix {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x x' : Path t d) (a : Fin t) (b j : ℕ) (hbj : b ≤ j)
    (hpre : ∀ k : Fin t, k.val < j → x k = x' k) :
    usedMass q x a b = usedMass q x' a b := by
  unfold usedMass
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkb : k.val < b
  · simp [hkb, hpre k (lt_of_lt_of_le hkb hbj)]
  · simp [hkb]

private theorem trackingError_eq_of_prefix {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x x' : Path t d) (b j : ℕ) (hbj : b ≤ j)
    (hpre : ∀ k : Fin t, k.val < j → x k = x' k) :
    trackingError q x b = trackingError q x' b := by
  unfold trackingError
  congr 1
  ext r
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro (hr | ⟨a, k, hk, rfl⟩)
    · exact Or.inl hr
    · right
      refine ⟨a, k, hk, ?_⟩
      rw [usedMass_eq_of_prefix q x x' a k.val j (le_trans hk hbj) hpre]
  · rintro (hr | ⟨a, k, hk, rfl⟩)
    · exact Or.inl hr
    · right
      refine ⟨a, k, hk, ?_⟩
      rw [usedMass_eq_of_prefix q x' x a k.val j (le_trans hk hbj)
        (fun k hk => (hpre k hk).symm)]

private theorem prefixValid_eq_of_prefix {d t : ℕ} (x x' : Path t d) (j : ℕ)
    (hpre : ∀ k : Fin t, k.val < j → x k = x' k) :
    PrefixValid x j ↔ PrefixValid x' j := by
  unfold PrefixValid
  constructor
  · rintro ⟨hv, hi⟩
    refine ⟨?_, ?_⟩
    · intro k hk
      simpa [hpre k hk] using hv k hk
    · intro i k hi' hk' heq
      exact hi i k hi' hk' (by
        calc
          x i = x' i := hpre i hi'
          _ = x' k := heq
          _ = x k := (hpre k hk').symm)
  · rintro ⟨hv, hi⟩
    refine ⟨?_, ?_⟩
    · intro k hk
      simpa [hpre k hk] using hv k hk
    · intro i k hi' hk' heq
      exact hi i k hi' hk' (by
        calc
          x' i = x i := (hpre i hi').symm
          _ = x k := heq
          _ = x' k := hpre k hk')

private theorem free_eq_of_prefix {d t : ℕ} (x x' : Path t d) (j : ℕ)
    (y : Fin d) (hpre : ∀ k : Fin t, k.val < j → x k = x' k) :
    Free x j y ↔ Free x' j y := by
  simp only [Free]
  constructor <;> intro h k hk
  · rw [← hpre k hk]
    exact h k hk
  · rw [hpre k hk]
    exact h k hk

private theorem availableMass_eq_of_prefix {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x x' : Path t d) (j : Fin t) (B : Finset (Fin d))
    (hpre : ∀ k : Fin t, k.val < j.val → x k = x' k) :
    availableMass q x j B = availableMass q x' j B := by
  unfold availableMass
  apply Finset.sum_congr rfl
  intro y hy
  have hf := free_eq_of_prefix x x' j.val y hpre
  by_cases h : Free x j.val y ∧ y ∉ B
  · simp [h, hf.mp h.1]
  · have h' : ¬ (Free x' j.val y ∧ y ∉ B) := by
      intro hh
      exact h ⟨hf.mpr hh.1, hh.2⟩
    simp [h, h']

private theorem ordinaryWeight_eq_of_prefix {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x x' : Path t d) (j : Fin t) (B : Finset (Fin d)) (z : Option (Fin d))
    (hpre : ∀ k : Fin t, k.val < j.val → x k = x' k) :
    ordinaryWeight q x j B z = ordinaryWeight q x' j B z := by
  have hv := prefixValid_eq_of_prefix x x' j.val hpre
  have he := trackingError_eq_of_prefix q x x' j.val j.val (le_rfl) hpre
  have hm := availableMass_eq_of_prefix q x x' j B hpre
  have hf : ∀ y, Free x j.val y ↔ Free x' j.val y :=
    fun y => free_eq_of_prefix x x' j.val y hpre
  have hactEq :
      (PrefixValid x j.val ∧ trackingError q x j.val ≤ (20 : ℝ)⁻¹ ∧
        0 < availableMass q x j B) ↔
      (PrefixValid x' j.val ∧ trackingError q x' j.val ≤ (20 : ℝ)⁻¹ ∧
        0 < availableMass q x' j B) := by
    constructor
    · rintro ⟨hvalid, hrest⟩
      rcases hrest with ⟨htrack, havail⟩
      exact ⟨hv.mp hvalid, by simpa [he] using htrack, by simpa [hm] using havail⟩
    · rintro ⟨hvalid, hrest⟩
      rcases hrest with ⟨htrack, havail⟩
      exact ⟨hv.mpr hvalid, by simpa [he] using htrack, by simpa [hm] using havail⟩
  unfold ordinaryWeight
  simp only [one_div]
  cases z with
  | none =>
    by_cases hactive : PrefixValid x j.val ∧ trackingError q x j.val ≤ (20 : ℝ)⁻¹ ∧
        0 < availableMass q x j B
    · have hactive' := hactEq.mp hactive
      simp [hactive, hactive']
    · have hactive' : ¬ (PrefixValid x' j.val ∧ trackingError q x' j.val ≤
          (20 : ℝ)⁻¹ ∧ 0 < availableMass q x' j B) := fun hh => hactive (hactEq.mpr hh)
      simp [hactive, hactive']
  | some y =>
    have hallowed : (Free x j.val y ∧ y ∉ B) ↔
        (Free x' j.val y ∧ y ∉ B) := by
      constructor
      · rintro ⟨hfree, hnot⟩
        exact ⟨(hf y).mp hfree, hnot⟩
      · rintro ⟨hfree, hnot⟩
        exact ⟨(hf y).mpr hfree, hnot⟩
    by_cases hactive : PrefixValid x j.val ∧ trackingError q x j.val ≤ (20 : ℝ)⁻¹ ∧
        0 < availableMass q x j B
    · have hactive' := hactEq.mp hactive
      by_cases ha : Free x j.val y ∧ y ∉ B
      · have ha' := hallowed.mp ha
        simp [hactive, hactive', ha, ha', hm]
      · have ha' : ¬ (Free x' j.val y ∧ y ∉ B) := fun hh => ha (hallowed.mpr hh)
        simp [hactive, hactive', ha, ha']
    · have hactive' : ¬ (PrefixValid x' j.val ∧ trackingError q x' j.val ≤
          (20 : ℝ)⁻¹ ∧ 0 < availableMass q x' j B) := fun hh => hactive (hactEq.mpr hh)
      simp [hactive, hactive']

private theorem ordinaryWeight_nonneg {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (hn : ∀ i y, 0 ≤ q i y) (x : Path t d) (j : Fin t)
    (B : Finset (Fin d)) (z : Option (Fin d)) :
    0 ≤ ordinaryWeight q x j B z := by
  classical
  unfold ordinaryWeight
  simp only [one_div]
  by_cases h : PrefixValid x j.val ∧ trackingError q x j.val ≤ (20 : ℝ)⁻¹ ∧
      0 < availableMass q x j B
  · rw [if_pos h]
    cases z with
    | none => simp
    | some y =>
      change 0 ≤ if Free x j.val y ∧ y ∉ B then
        q j y / availableMass q x j B else 0
      by_cases ha : Free x j.val y ∧ y ∉ B
      · simp only [if_pos ha]
        exact div_nonneg (hn j y) (le_of_lt h.2.2)
      · simp only [if_neg ha]
        norm_num
  · rw [if_neg h]
    by_cases hz : z = none <;> simp [hz]

private theorem ordinaryWeight_sum_one {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (j : Fin t) (B : Finset (Fin d))
    (hn : ∀ i y, 0 ≤ q i y) :
    ∑ z, ordinaryWeight q x j B z = 1 := by
  classical
  by_cases ha : PrefixValid x j.val ∧ trackingError q x j.val ≤ (20 : ℝ)⁻¹ ∧
      0 < availableMass q x j B
  · have hdiv :
        (∑ y : Fin d, if Free x j.val y ∧ y ∉ B then
          q j y / availableMass q x j B else 0) = 1 := by
      calc
        (∑ y : Fin d, if Free x j.val y ∧ y ∉ B then
            q j y / availableMass q x j B else 0) =
            ∑ y : Fin d,
              (if Free x j.val y ∧ y ∉ B then q j y else 0) /
                availableMass q x j B := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hallowed : Free x j.val y ∧ y ∉ B <;> simp [hallowed]
        _ = (∑ y : Fin d, if Free x j.val y ∧ y ∉ B then q j y else 0) /
              availableMass q x j B := by rw [Finset.sum_div]
        _ = 1 := by
          rw [show (∑ y : Fin d, if Free x j.val y ∧ y ∉ B then q j y else 0) =
            availableMass q x j B by rfl]
          exact div_self (ne_of_gt ha.2.2)
    unfold ordinaryWeight
    simp only [one_div, if_pos ha, Fintype.sum_option]
    simpa [hdiv]
  · unfold ordinaryWeight
    simp only [one_div, if_neg ha, Fintype.sum_option]
    simp

private theorem trackingError_ge_abs {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (b : ℕ) (a : Fin t) (k : Fin (t + 1)) (hk : k.val ≤ b) :
    |usedMass q x a k.val - (k.val : ℝ) / d| ≤ trackingError q x b := by
  classical
  unfold trackingError
  have hfinite :
      ({0} ∪ {r | ∃ a : Fin t, ∃ k : Fin (t + 1),
        k.val ≤ b ∧ r = |usedMass q x a k.val - (k.val : ℝ) / d|}).Finite := by
    apply Set.Finite.union
    · exact Set.finite_singleton 0
    · refine Set.Finite.subset (Set.finite_range fun p : Fin t × Fin (t + 1) =>
          |usedMass q x p.1 p.2.val - (p.2.val : ℝ) / d|) ?_
      intro r hr
      rcases hr with ⟨a, k, hk', rfl⟩
      exact Set.mem_range.mpr ⟨(a, k), rfl⟩
  exact le_csSup hfinite.bddAbove (Or.inr ⟨a, k, hk, rfl⟩)

private theorem trackingError_nonneg {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (b : ℕ) : 0 ≤ trackingError q x b := by
  classical
  unfold trackingError
  have hfinite :
      ({0} ∪ {r | ∃ a : Fin t, ∃ k : Fin (t + 1),
        k.val ≤ b ∧ r = |usedMass q x a k.val - (k.val : ℝ) / d|}).Finite := by
    apply Set.Finite.union
    · exact Set.finite_singleton 0
    · refine Set.Finite.subset (Set.finite_range fun p : Fin t × Fin (t + 1) =>
          |usedMass q x p.1 p.2.val - (p.2.val : ℝ) / d|) ?_
      intro r hr
      rcases hr with ⟨a, k, hk, rfl⟩
      exact Set.mem_range.mpr ⟨(a, k), rfl⟩
  exact le_csSup hfinite.bddAbove (Or.inl rfl)

private theorem trackingError_mono {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) {b b' : ℕ} (hbb : b ≤ b') :
    trackingError q x b ≤ trackingError q x b' := by
  classical
  unfold trackingError
  have hfinite (c : ℕ) :
      ({0} ∪ {r | ∃ a : Fin t, ∃ k : Fin (t + 1),
        k.val ≤ c ∧ r = |usedMass q x a k.val - (k.val : ℝ) / d|}).Finite := by
    apply Set.Finite.union
    · exact Set.finite_singleton 0
    · refine Set.Finite.subset (Set.finite_range fun p : Fin t × Fin (t + 1) =>
          |usedMass q x p.1 p.2.val - (p.2.val : ℝ) / d|) ?_
      intro r hr
      rcases hr with ⟨a, k, hk, rfl⟩
      exact Set.mem_range.mpr ⟨(a, k), rfl⟩
  refine csSup_le ⟨0, Or.inl rfl⟩ ?_
  intro r hr
  apply le_csSup (hfinite b').bddAbove
  rcases hr with hzero | ⟨a, k, hk, hr⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨a, k, le_trans hk hbb, hr⟩

private theorem Free_antitone {d t : ℕ} (x : Path t d) {b b' : ℕ}
    (hbb : b ≤ b') (y : Fin d) : Free x b' y → Free x b y := by
  intro h k hk
  exact h k (lt_of_lt_of_le hk hbb)

private theorem indicatorProduct_variation_bound (m : ℕ) (E I : ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hE0 : ∀ r, 0 ≤ E r)
    (hEmono : ∀ r, E r ≤ E (r + 1)) (hEbound : ∀ r, r < m → E r ≤ C)
    (hI01 : ∀ r, I r = 0 ∨ I r = 1) (hImono : ∀ r, I (r + 1) ≤ I r) :
    ∑ r ∈ Finset.range (m - 1), |E (r + 1) * I (r + 1) - E r * I r| ≤ 2 * C := by
  classical
  by_cases hm : m = 0
  · simp [hm, hC]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hlast : m - 1 < m := Nat.sub_lt (Nat.pos_of_ne_zero hm) (by decide)
    have hfirst :
        (∑ r ∈ Finset.range (m - 1), I (r + 1) * (E (r + 1) - E r)) ≤ C := by
      calc
        _ ≤ ∑ r ∈ Finset.range (m - 1), (E (r + 1) - E r) := by
          apply Finset.sum_le_sum
          intro r hr
          have hIle : I (r + 1) ≤ 1 := by
            rcases hI01 (r + 1) with h | h <;> simp [h]
          have hdiff : 0 ≤ E (r + 1) - E r := sub_nonneg.mpr (hEmono r)
          nlinarith [mul_le_mul_of_nonneg_right hIle hdiff]
        _ = E (m - 1) - E 0 := Finset.sum_range_sub E (m - 1)
        _ ≤ C := by linarith [hEbound (m - 1) hlast, hE0 0]
    have hsecond :
        (∑ r ∈ Finset.range (m - 1), E r * (I r - I (r + 1))) ≤ C := by
      calc
        _ ≤ ∑ r ∈ Finset.range (m - 1), C * (I r - I (r + 1)) := by
          apply Finset.sum_le_sum
          intro r hr
          have hdiff : 0 ≤ I r - I (r + 1) := sub_nonneg.mpr (hImono r)
          have hrm : r < m := lt_trans (Finset.mem_range.mp hr) hlast
          exact mul_le_mul_of_nonneg_right (hEbound r hrm) hdiff
        _ = C * (I 0 - I (m - 1)) := by
          rw [← Finset.mul_sum]
          have hsumdiff :
              (Finset.range (m - 1)).sum (fun r => I r - I (r + 1)) =
                I 0 - I (m - 1) := by
            have hterm :
                (Finset.range (m - 1)).sum (fun r => I r - I (r + 1)) =
                  - (Finset.range (m - 1)).sum (fun r => I (r + 1) - I r) := by
              calc
                (Finset.range (m - 1)).sum (fun r => I r - I (r + 1)) =
                    (Finset.range (m - 1)).sum (fun r => -(I (r + 1) - I r)) := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  ring
                _ = - (Finset.range (m - 1)).sum (fun r => I (r + 1) - I r) := by
                  rw [Finset.sum_neg_distrib]
            rw [hterm, Finset.sum_range_sub I (m - 1)]
            ring
          rw [hsumdiff]
        _ ≤ C := by
          have hI0 : I 0 ≤ 1 := by rcases hI01 0 with h | h <;> simp [h]
          have hIl : 0 ≤ I (m - 1) := by rcases hI01 (m - 1) with h | h <;> simp [h]
          have hdiffI : I 0 - I (m - 1) ≤ 1 := by linarith
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiffI hC
    calc
      (∑ r ∈ Finset.range (m - 1), |E (r + 1) * I (r + 1) - E r * I r|) ≤
          (∑ r ∈ Finset.range (m - 1), I (r + 1) * (E (r + 1) - E r)) +
            ∑ r ∈ Finset.range (m - 1), E r * (I r - I (r + 1)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro r hr
        have hIpos : 0 ≤ I (r + 1) := by rcases hI01 (r + 1) with h | h <;> simp [h]
        have hEpos : 0 ≤ E r := hE0 r
        have hEdiff : 0 ≤ E (r + 1) - E r := sub_nonneg.mpr (hEmono r)
        have hIdiff : 0 ≤ I r - I (r + 1) := sub_nonneg.mpr (hImono r)
        have hform : E (r + 1) * I (r + 1) - E r * I r =
            I (r + 1) * (E (r + 1) - E r) + E r * (I (r + 1) - I r) := by ring
        have hA : 0 ≤ I (r + 1) * (E (r + 1) - E r) := mul_nonneg hIpos hEdiff
        have hB : E r * (I (r + 1) - I r) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hEpos (sub_nonpos.mpr (hImono r))
        have hAbs : |I (r + 1) * (E (r + 1) - E r) +
              E r * (I (r + 1) - I r)| ≤
            I (r + 1) * (E (r + 1) - E r) + E r * (I r - I (r + 1)) := by
          rw [abs_le]
          constructor <;> linarith
        rw [hform]
        exact hAbs
      _ ≤ C + C := add_le_add hfirst hsecond
      _ = 2 * C := by ring

/-- All targets with queried steps strictly later than the ordinary step. -/
def pendingLabels {d t : ℕ} (S : Finset (Fin t)) (y : Fin t → Fin d)
    (j : Fin t) : Finset (Fin d) := (S.filter (fun i => j.val < i.val)).image y

noncomputable def forcingStepWeight {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d)
    (j : Fin t) (z : Option (Fin d)) : ℝ :=
  if j ∈ S then
    if PrefixValid x j.val ∧ trackingError q x j.val ≤ 1 / 20 ∧ Free x j.val (y j)
    then if z = some (y j) then 1 else 0
    else if z = none then 1 else 0
  else ordinaryWeight q x j (pendingLabels S y j) z

noncomputable def forcingWeight {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) : ℝ :=
  ∏ j, forcingStepWeight q S y x j (x j)

/-- The two normalization nodes concern explicit triangular kernel products. -/
theorem sequential_weights_probability {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (hn : ∀ i y, 0 ≤ q i y) (hs : ∀ i, ∑ y, q i y = 1) :
    (∀ x, 0 ≤ sequentialWeight q x) ∧ (∑ x, sequentialWeight q x = 1) := by
  classical
  constructor
  · intro x
    unfold sequentialWeight
    apply Finset.prod_nonneg
    intro j hj
    exact ordinaryWeight_nonneg q hn x j ∅ (x j)
  · let K : ∀ j : Fin t, (Fin j → Option (Fin d)) → Option (Fin d) → ℝ :=
      fun j p z => ordinaryWeight q (pathOfPrefix j p) j ∅ z
    have hK : ∀ j p, ∑ z, K j p z = 1 := by
      intro j p
      exact ordinaryWeight_sum_one q (pathOfPrefix j p) j ∅ hn
    have htri := triangularKernelSum t K hK
    calc
      ∑ x, sequentialWeight q x =
          ∑ x : Path t d, ∏ j, K j (prefixOf x j) (x j) := by
        apply Finset.sum_congr rfl
        intro x hx
        unfold sequentialWeight
        apply Finset.prod_congr rfl
        intro j hj
        symm
        apply ordinaryWeight_eq_of_prefix q (pathOfPrefix j (prefixOf x j)) x j ∅ (x j)
        intro k hk
        simp [pathOfPrefix, prefixOf, hk]
      _ = 1 := htri

private theorem forcingStepWeight_nonneg {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (hn : ∀ i y, 0 ≤ q i y) (S : Finset (Fin t)) (y : Fin t → Fin d)
    (x : Path t d) (j : Fin t) (z : Option (Fin d)) :
    0 ≤ forcingStepWeight q S y x j z := by
  classical
  unfold forcingStepWeight
  simp only [one_div]
  by_cases hj : j ∈ S
  · rw [if_pos hj]
    by_cases hf : PrefixValid x j.val ∧ trackingError q x j.val ≤ (20 : ℝ)⁻¹ ∧
        Free x j.val (y j)
    · rw [if_pos hf]
      by_cases hz : z = some (y j) <;> simp [hz]
    · rw [if_neg hf]
      by_cases hz : z = none <;> simp [hz]
  · rw [if_neg hj]
    exact ordinaryWeight_nonneg q hn x j (pendingLabels S y j) z

private theorem forcingStepWeight_sum_one {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (hn : ∀ i y, 0 ≤ q i y) (S : Finset (Fin t)) (y : Fin t → Fin d)
    (x : Path t d) (j : Fin t) :
    ∑ z, forcingStepWeight q S y x j z = 1 := by
  classical
  by_cases hj : j ∈ S
  · by_cases hf : PrefixValid x j.val ∧ trackingError q x j.val ≤ 1 / 20 ∧
        Free x j.val (y j)
    · simp [forcingStepWeight, hj, hf, one_div]
    · simp [forcingStepWeight, hj, hf, one_div]
  · simp [forcingStepWeight, hj, ordinaryWeight_sum_one q x j
      (pendingLabels S y j) hn, one_div]

private theorem forcingStepWeight_eq_of_prefix {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x x' : Path t d) (j : Fin t)
    (z : Option (Fin d)) (hpre : ∀ k : Fin t, k.val < j.val → x k = x' k) :
    forcingStepWeight q S y x j z = forcingStepWeight q S y x' j z := by
  have hv := prefixValid_eq_of_prefix x x' j.val hpre
  have he := trackingError_eq_of_prefix q x x' j.val j.val le_rfl hpre
  have hf := free_eq_of_prefix x x' j.val (y j) hpre
  by_cases hj : j ∈ S
  · have hforce :
        (PrefixValid x j.val ∧ trackingError q x j.val ≤ 1 / 20 ∧ Free x j.val (y j)) ↔
          (PrefixValid x' j.val ∧ trackingError q x' j.val ≤ 1 / 20 ∧
            Free x' j.val (y j)) := by
      constructor
      · rintro ⟨hvalid, hrest⟩
        rcases hrest with ⟨htrack, hfree⟩
        exact ⟨hv.mp hvalid, by simpa [he] using htrack, (hf).mp hfree⟩
      · rintro ⟨hvalid, hrest⟩
        rcases hrest with ⟨htrack, hfree⟩
        exact ⟨hv.mpr hvalid, by simpa [he] using htrack, (hf).mpr hfree⟩
    by_cases hcx : PrefixValid x j.val ∧ trackingError q x j.val ≤ 1 / 20 ∧
        Free x j.val (y j)
    · have hcx' := hforce.mp hcx
      have hcxNorm : PrefixValid x j.val ∧ trackingError q x j.val ≤ (20 : ℝ)⁻¹ ∧
          Free x j.val (y j) := by simpa [one_div] using hcx
      have hcx'Norm : PrefixValid x' j.val ∧ trackingError q x' j.val ≤ (20 : ℝ)⁻¹ ∧
          Free x' j.val (y j) := by simpa [one_div] using hcx'
      simp [forcingStepWeight, hj, hcxNorm, hcx'Norm, one_div]
    · have hcx' : ¬ (PrefixValid x' j.val ∧ trackingError q x' j.val ≤ 1 / 20 ∧
          Free x' j.val (y j)) := fun hh => hcx (hforce.mpr hh)
      have hcxNorm : ¬ (PrefixValid x j.val ∧ trackingError q x j.val ≤ (20 : ℝ)⁻¹ ∧
          Free x j.val (y j)) := by simpa [one_div] using hcx
      have hcx'Norm : ¬ (PrefixValid x' j.val ∧ trackingError q x' j.val ≤ (20 : ℝ)⁻¹ ∧
          Free x' j.val (y j)) := by simpa [one_div] using hcx'
      simp [forcingStepWeight, hj, hcxNorm, hcx'Norm, one_div]
  · simp [forcingStepWeight, hj, ordinaryWeight_eq_of_prefix q x x' j
      (pendingLabels S y j) z hpre]

theorem forcing_weights_probability {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (hn : ∀ i y, 0 ≤ q i y) (hs : ∀ i, ∑ y, q i y = 1)
    (S : Finset (Fin t)) (y : Fin t → Fin d) :
    (∀ x, 0 ≤ forcingWeight q S y x) ∧ (∑ x, forcingWeight q S y x = 1) := by
  classical
  constructor
  · intro x
    unfold forcingWeight
    apply Finset.prod_nonneg
    intro j hj
    exact forcingStepWeight_nonneg q hn S y x j (x j)
  · let K : ∀ j : Fin t, (Fin j → Option (Fin d)) → Option (Fin d) → ℝ :=
      fun j p z => forcingStepWeight q S y (pathOfPrefix j p) j z
    have hK : ∀ j p, ∑ z, K j p z = 1 := by
      intro j p
      exact forcingStepWeight_sum_one q hn S y (pathOfPrefix j p) j
    have htri := triangularKernelSum t K hK
    calc
      ∑ x, forcingWeight q S y x =
          ∑ x : Path t d, ∏ j, K j (prefixOf x j) (x j) := by
        apply Finset.sum_congr rfl
        intro x hx
        unfold forcingWeight
        apply Finset.prod_congr rfl
        intro j hj
        have hpre : ∀ k : Fin t, k.val < j.val →
            x k = pathOfPrefix j (prefixOf x j) k := by
          intro k hk
          simp [pathOfPrefix, prefixOf, hk]
        exact forcingStepWeight_eq_of_prefix q S y x
          (pathOfPrefix j (prefixOf x j)) j (x j) hpre
      _ = 1 := htri

noncomputable def sequentialLaw {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (hn : ∀ i y, 0 ≤ q i y) (hs : ∀ i, ∑ y, q i y = 1) : FinProb (Path t d) :=
  ⟨sequentialWeight q, (sequential_weights_probability q hn hs).1,
    (sequential_weights_probability q hn hs).2⟩

noncomputable def forcingLaw {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (hn : ∀ i y, 0 ≤ q i y) (hs : ∀ i, ∑ y, q i y = 1)
    (S : Finset (Fin t)) (y : Fin t → Fin d) : FinProb (Path t d) :=
  ⟨forcingWeight q S y, (forcing_weights_probability q hn hs S y).1,
    (forcing_weights_probability q hn hs S y).2⟩

/-- `G` includes validity and the terminal time, and explicitly excludes stops. -/
def Good {d t : ℕ} (q : Fin t → Fin d → ℝ) (x : Path t d) : Prop :=
  PrefixValid x t ∧ trackingError q x t ≤ 1 / 20 ∧
    trackingError q x t ≤ (d : ℝ) ^ (-(0.1 : ℝ))

def RunningThrough {d t : ℕ} (q : Fin t → Fin d → ℝ) (x : Path t d) (b : ℕ) : Prop :=
  PrefixValid x b ∧ ∀ j : Fin t, j.val < b → trackingError q x j.val ≤ 1 / 20

noncomputable def failureBound (d : ℕ) : ℝ := Real.exp (-((d : ℝ) ^ (0.1 : ℝ)))
noncomputable def relativeError (d : ℕ) : ℝ := (d : ℝ) ^ (-(0.09 : ℝ))

def readLabels {d t : ℕ} (hd : 0 < d) (x : Path t d) : Fin t → Fin d :=
  fun i => (x i).getD ⟨0, hd⟩

noncomputable def conditionedLaw {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (h : OrderedInput d t q)
    (hG : 0 < (sequentialLaw q h.nonneg h.row_sum).pr (Good q)) :
    FinProb (Fin t → Fin d) :=
  FinProb.map (FinProb.cond (sequentialLaw q h.nonneg h.row_sum) (Good q) hG)
    (readLabels (by have := h.dimension; omega))

/-- Actual kernel drifts, including absorbing failure continuations. -/
noncomputable def stepDrift {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (a j : Fin t) : ℝ :=
  ∑ z, ordinaryWeight q x j ∅ z * z.elim 0 (q a)

noncomputable def forcedStepDrift {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) (a j : Fin t) : ℝ :=
  ∑ z, forcingStepWeight q S y x j z * z.elim 0 (q a)

noncomputable def martingalePart {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x : Path t d) (a : Fin t) (b : ℕ) : ℝ :=
  ∑ j : Fin t, if j.val < b then (x j).elim 0 (q a) - stepDrift q x a j else 0

noncomputable def forcedMartingalePart {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) (a : Fin t) (b : ℕ) : ℝ :=
  ∑ j : Fin t, if j.val < b then
    (x j).elim 0 (q a) - forcedStepDrift q S y x a j else 0

def MartingaleGood {d t : ℕ} (q : Fin t → Fin d → ℝ) (x : Path t d) : Prop :=
  ∀ a (b : Fin (t + 1)), |martingalePart q x a b.val| ≤ (d : ℝ) ^ (-(1 / 8 : ℝ))

def ForcedMartingaleGood {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) : Prop :=
  ∀ a (b : Fin (t + 1)),
    |forcedMartingalePart q S y x a b.val| ≤ (1 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 8 : ℝ))

/-- TeX 03:662: free mass is `1-D`, bounded away from zero before a stop. -/
theorem free_mass_before_stop {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (h : OrderedInput d t q) (x : Path t d) (j : Fin t)
    (hv : PrefixValid x j.val) (he : trackingError q x j.val ≤ 1 / 20) :
    availableMass q x j ∅ = 1 - usedMass q x j j.val ∧
      1 / 5 ≤ availableMass q x j ∅ := by
  classical
  obtain ⟨hvalid, hinj⟩ := hv
  have hd : 0 < d := by have := h.dimension; omega
  let y₀ : Fin d := ⟨0, hd⟩
  let S : Finset (Fin t) := Finset.univ.filter (fun k => k.val < j.val)
  let f : Fin t → Fin d := fun k => (x k).getD y₀
  let U : Finset (Fin d) := S.image f
  have hfSome (k : Fin t) (hk : k ∈ S) : ∃ y, x k = some y := by
    exact hvalid k (Finset.mem_filter.mp hk).2
  have hfEq (k : Fin t) (hk : k ∈ S) : x k = some (f k) := by
    obtain ⟨y, hy⟩ := hfSome k hk
    simpa [f, hy] using hy
  have hinjS : Set.InjOn f S := by
    intro k hk l hl hkl
    apply hinj k l (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2
    rw [hfEq k hk, hfEq l hl, hkl]
  have hfree (y : Fin d) : Free x j.val y ↔ y ∉ U := by
    constructor
    · intro hy hmem
      rcases Finset.mem_image.mp hmem with ⟨k, hk, rfl⟩
      exact hy k (Finset.mem_filter.mp hk).2 (hfEq k hk)
    · intro hy k hk hxy
      have hks : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
      apply hy
      apply Finset.mem_image.mpr
      refine ⟨k, hks, ?_⟩
      obtain ⟨z, hz⟩ := hvalid k hk
      have hz' : z = y := by simpa [hz] using congrArg (fun v : Option (Fin d) => v.getD y₀) hxy
      simpa [f, hz] using hz'
  have havail : availableMass q x j ∅ = ∑ y ∈ Uᶜ, q j y := by
    unfold availableMass
    calc
      (∑ y : Fin d, if Free x j.val y ∧ y ∉ (∅ : Finset (Fin d)) then q j y else 0) =
          ∑ y : Fin d, if y ∈ Uᶜ then q j y else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hU : y ∈ U <;> simp [hfree y, hU]
      _ = ∑ y ∈ Uᶜ, q j y := by
        rw [← Finset.sum_filter]
        congr 1
        ext y
        simp
  have hused : usedMass q x j j.val = ∑ k ∈ S, q j (f k) := by
    unfold usedMass
    calc
      (∑ k : Fin t, if k.val < j.val then (x k).elim 0 (q j) else 0) =
          ∑ k : Fin t, if k ∈ S then q j (f k) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hks : k ∈ S
        · have hlt := (Finset.mem_filter.mp hks).2
          obtain ⟨z, hz⟩ := hvalid k hlt
          simp [hks, hlt, f, hz]
        · have hge : ¬ k.val < j.val := by simpa [S] using hks
          simp [hks, hge]
      _ = ∑ k ∈ S, q j (f k) := by simp
  have himage : ∑ y ∈ U, q j y = ∑ k ∈ S, q j (f k) := by
    simp [U, Finset.sum_image hinjS]
  have hsplit : (∑ y ∈ U, q j y) + (∑ y ∈ Uᶜ, q j y) = 1 := by
    calc
      (∑ y ∈ U, q j y) + (∑ y ∈ Uᶜ, q j y) = ∑ y, q j y :=
        Finset.sum_add_sum_compl U (q j)
      _ = 1 := h.row_sum j
  have hmain : availableMass q x j ∅ = 1 - usedMass q x j j.val := by
    calc
      availableMass q x j ∅ = ∑ y ∈ Uᶜ, q j y := havail
      _ = 1 - ∑ y ∈ U, q j y := by linarith [hsplit]
      _ = 1 - usedMass q x j j.val := by rw [himage, ← hused]
  refine ⟨hmain, ?_⟩
  have htrack := trackingError_ge_abs q x j.val j ⟨j.val, by omega⟩ (by rfl)
  have hupper : usedMass q x j j.val ≤ (j.val : ℝ) / d + 1 / 20 := by
    have h := abs_le.mp (htrack.trans he)
    linarith
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hjt : (j.val : ℝ) ≤ (t : ℝ) := by exact_mod_cast j.isLt.le
  have hjd : (j.val : ℝ) / d ≤ 3 / 4 := by
    apply (div_le_iff₀ hdR).2
    have hjbound : (j.val : ℝ) ≤ 3 * (d : ℝ) / 4 := le_trans hjt h.horizon
    nlinarith [hjbound]
  rw [hmain]
  linarith

private theorem free_row_mass_eq {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (a : Fin t) (hrow : ∑ y, q a y = 1) (x : Path t d) (j : Fin t)
    (hd : 0 < d) (hv : PrefixValid x j.val) :
    (∑ y, if Free x j.val y then q a y else 0) = 1 - usedMass q x a j.val := by
  classical
  obtain ⟨hvalid, hinj⟩ := hv
  let y₀ : Fin d := ⟨0, hd⟩
  let S : Finset (Fin t) := Finset.univ.filter (fun k => k.val < j.val)
  let f : Fin t → Fin d := fun k => (x k).getD y₀
  let U : Finset (Fin d) := S.image f
  have hfEq (k : Fin t) (hk : k ∈ S) : x k = some (f k) := by
    obtain ⟨z, hz⟩ := hvalid k (Finset.mem_filter.mp hk).2
    simpa [f, hz] using hz
  have hinjS : Set.InjOn f S := by
    intro k hk l hl hkl
    apply hinj k l (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2
    rw [hfEq k hk, hfEq l hl, hkl]
  have hfree (y : Fin d) : Free x j.val y ↔ y ∉ U := by
    constructor
    · intro hy hmem
      rcases Finset.mem_image.mp hmem with ⟨k, hk, rfl⟩
      exact hy k (Finset.mem_filter.mp hk).2 (hfEq k hk)
    · intro hy k hk hxy
      have hks : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
      apply hy
      apply Finset.mem_image.mpr
      refine ⟨k, hks, ?_⟩
      obtain ⟨z, hz⟩ := hvalid k hk
      have hzy : z = y := by
        simpa [hz] using congrArg (fun v : Option (Fin d) => v.getD y₀) hxy
      simpa [f, hz] using hzy
  have havail :
      (∑ y : Fin d, if Free x j.val y then q a y else 0) = ∑ y ∈ Uᶜ, q a y := by
    calc
      (∑ y : Fin d, if Free x j.val y then q a y else 0) =
          ∑ y : Fin d, if y ∈ Uᶜ then q a y else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hU : y ∈ U <;> simp [hfree y, hU]
      _ = ∑ y ∈ Uᶜ, q a y := by
        rw [← Finset.sum_filter]
        congr 1
        ext y
        simp
  have hused : usedMass q x a j.val = ∑ k ∈ S, q a (f k) := by
    unfold usedMass
    calc
      (∑ k : Fin t, if k.val < j.val then (x k).elim 0 (q a) else 0) =
          ∑ k : Fin t, if k ∈ S then q a (f k) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hks : k ∈ S
        · have hlt := (Finset.mem_filter.mp hks).2
          obtain ⟨z, hz⟩ := hvalid k hlt
          simp [hks, hlt, f, hz]
        · have hge : ¬ k.val < j.val := by simpa [S] using hks
          simp [hks, hge]
      _ = ∑ k ∈ S, q a (f k) := by simp
  have himage : ∑ y ∈ U, q a y = ∑ k ∈ S, q a (f k) := by
    simp [U, Finset.sum_image hinjS]
  have hsplit : (∑ y ∈ U, q a y) + (∑ y ∈ Uᶜ, q a y) = 1 := by
    calc
      (∑ y ∈ U, q a y) + (∑ y ∈ Uᶜ, q a y) = ∑ y, q a y :=
        Finset.sum_add_sum_compl U (q a)
      _ = 1 := hrow
  calc
    (∑ y : Fin d, if Free x j.val y then q a y else 0) = ∑ y ∈ Uᶜ, q a y := havail
    _ = 1 - ∑ y ∈ U, q a y := by linarith [hsplit]
    _ = 1 - usedMass q x a j.val := by rw [himage, ← hused]

/-- TeX 03:663–668: exact drift and the bounded centered increment. -/
theorem sequential_drift_increment {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (h : OrderedInput d t q) (x : Path t d) (a j : Fin t)
    (hv : PrefixValid x j.val) (he : trackingError q x j.val ≤ 1 / 20) :
    stepDrift q x a j =
      (∑ y, if Free x j.val y then q a y * q j y else 0) /
        (1 - usedMass q x j j.val) ∧
    ∀ z, ordinaryWeight q x j ∅ z ≠ 0 →
      |z.elim 0 (q a) - stepDrift q x a j| ≤
        20 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
  classical
  obtain ⟨hmass, hpositive⟩ := free_mass_before_stop q h x j hv he
  have hpos : 0 < availableMass q x j ∅ := by linarith
  have hactive : PrefixValid x j.val ∧ trackingError q x j.val ≤ 1 / 20 ∧
      0 < availableMass q x j ∅ := ⟨hv, he, hpos⟩
  have hactive' : PrefixValid x j.val ∧ trackingError q x j.val ≤ (20 : ℝ)⁻¹ ∧
      0 < availableMass q x j ∅ := by simpa [one_div] using hactive
  have hmass' : availableMass q x j ∅ = 1 - usedMass q x j j.val := hmass
  have hdrift : 0 ≤ stepDrift q x a j ∧
      stepDrift q x a j ≤ 10 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
    let M : ℝ := 10 * (d : ℝ) ^ (-(0.95 : ℝ))
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hsum : ∑ z, ordinaryWeight q x j ∅ z = 1 :=
      ordinaryWeight_sum_one q x j ∅ h.nonneg
    constructor
    · unfold stepDrift
      apply Finset.sum_nonneg
      intro z hz
      exact mul_nonneg (ordinaryWeight_nonneg q h.nonneg x j ∅ z) (by
        cases z with
        | none => simp
        | some y => exact h.nonneg a y)
    · calc
        stepDrift q x a j =
            ∑ z, ordinaryWeight q x j ∅ z * z.elim 0 (q a) := rfl
        _ ≤ ∑ z, ordinaryWeight q x j ∅ z * M := by
          apply Finset.sum_le_sum
          intro z hz
          apply mul_le_mul_of_nonneg_left _
            (ordinaryWeight_nonneg q h.nonneg x j ∅ z)
          cases z with
          | none => exact hM
          | some y => exact h.atom a y
        _ = M := by rw [← Finset.sum_mul, hsum, one_mul]
  have hformula :
      stepDrift q x a j =
        (∑ y, if Free x j.val y then q a y * q j y else 0) /
          availableMass q x j ∅ := by
    unfold stepDrift
    calc
      (∑ z, ordinaryWeight q x j ∅ z * z.elim 0 (q a)) =
          ∑ y : Fin d, if Free x j.val y then
            (q j y / availableMass q x j ∅) * q a y else 0 := by
        rw [Fintype.sum_option]
        unfold ordinaryWeight
        simp only [one_div, if_pos hactive']
        simp
      _ = (∑ y, if Free x j.val y then q a y * q j y else 0) /
            availableMass q x j ∅ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro y hy
        split_ifs <;> ring
  refine ⟨?_, ?_⟩
  · rw [hformula, hmass']
  · intro z hz
    have hdlo := hdrift.1
    have hdhi := hdrift.2
    have hM : 0 ≤ 10 * (d : ℝ) ^ (-(0.95 : ℝ)) := by positivity
    cases z with
    | none =>
      have hzero : ordinaryWeight q x j ∅ none = 0 := by
        simp [ordinaryWeight, hactive', one_div]
      exact False.elim (hz hzero)
    | some y =>
      have hylo : 0 ≤ q a y := h.nonneg a y
      have hyhi : q a y ≤ 10 * (d : ℝ) ^ (-(0.95 : ℝ)) := h.atom a y
      have hcenter : |q a y - stepDrift q x a j| ≤
          10 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
        rw [abs_le]
        constructor <;> linarith
      calc
        |(some y).elim 0 (q a) - stepDrift q x a j| ≤
            10 * (d : ℝ) ^ (-(0.95 : ℝ)) := by simpa using hcenter
        _ ≤ 20 * (d : ℝ) ^ (-(0.95 : ℝ)) := by linarith

/-- TeX 03:668–671: simultaneous stopped martingale concentration. -/
theorem sequential_martingale_concentration :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ) (h : OrderedInput d t q),
      1 - failureBound d ≤ (sequentialLaw q h.nonneg h.row_sum).pr (MartingaleGood q) := by
  sorry

private theorem sum_range_abel_bound (m : ℕ) (f g : ℕ → ℝ) (ε C V : ℝ)
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (hprefix : ∀ k, k ≤ m → |∑ r ∈ Finset.range k, g r| ≤ ε)
    (hend : |f (m - 1)| ≤ C)
    (hvariation : ∑ r ∈ Finset.range (m - 1), |f (r + 1) - f r| ≤ V) :
    |∑ r ∈ Finset.range m, f r * g r| ≤ C * ε + V * ε := by
  classical
  let G : ℕ → ℝ := fun k => ∑ r ∈ Finset.range k, g r
  by_cases hm : m = 0
  · subst m
    simp [G]
    positivity
  · have hparts :
        (∑ r ∈ Finset.range m, f r * g r) =
          f (m - 1) * G m -
            ∑ r ∈ Finset.range (m - 1), (f (r + 1) - f r) * G (r + 1) := by
      simpa [G, smul_eq_mul] using (Finset.sum_range_by_parts f g m)
    have hfirst : |f (m - 1) * G m| ≤ C * ε := by
      rw [abs_mul]
      exact mul_le_mul hend (hprefix m le_rfl) (abs_nonneg _) hC
    have hsecond :
        |∑ r ∈ Finset.range (m - 1), (f (r + 1) - f r) * G (r + 1)| ≤ V * ε := by
      calc
        |∑ r ∈ Finset.range (m - 1), (f (r + 1) - f r) * G (r + 1)| ≤
          ∑ r ∈ Finset.range (m - 1),
              |f (r + 1) - f r| * |G (r + 1)| := by
          simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
            (fun r : ℕ => (f (r + 1) - f r) * G (r + 1)) (Finset.range (m - 1))
        _ ≤ ∑ r ∈ Finset.range (m - 1),
            |f (r + 1) - f r| * ε := by
          apply Finset.sum_le_sum
          intro r hr
          have hrm : r + 1 ≤ m := by
            have := Finset.mem_range.mp hr
            omega
          have hG : |G (r + 1)| ≤ ε := by simpa [G] using hprefix (r + 1) hrm
          exact mul_le_mul_of_nonneg_left hG (abs_nonneg _)
        _ = ε * ∑ r ∈ Finset.range (m - 1), |f (r + 1) - f r| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring
        _ ≤ ε * V := mul_le_mul_of_nonneg_left hvariation hε
        _ = V * ε := by ring
    calc
      |∑ r ∈ Finset.range m, f r * g r| =
          |f (m - 1) * G m -
            ∑ r ∈ Finset.range (m - 1), (f (r + 1) - f r) * G (r + 1)| := by rw [hparts]
      _ ≤ |f (m - 1) * G m| +
          |∑ r ∈ Finset.range (m - 1), (f (r + 1) - f r) * G (r + 1)| := by
            simpa using abs_sub_le (f (m - 1) * G m) 0
              (∑ r ∈ Finset.range (m - 1), (f (r + 1) - f r) * G (r + 1))
      _ ≤ C * ε + V * ε := add_le_add hfirst hsecond

private theorem orderedColumnRangeError {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (h : OrderedInput d t q) (k : ℕ) (hk : k ≤ t) (y : Fin d) :
    |(∑ r ∈ Finset.range k,
        (if hr : r < t then q ⟨r, hr⟩ y else 0)) - (k : ℝ) / d| ≤
      10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
  classical
  have hk' : k < t + 1 := by omega
  have hsum :
      (∑ j : Fin t, if j.val < k then q j y else 0) =
        ∑ r ∈ Finset.range k, (if hr : r < t then q ⟨r, hr⟩ y else 0) := by
    calc
      (∑ j : Fin t, if j.val < k then q j y else 0) =
          ∑ r ∈ Finset.range t,
            if r < k then (if hr : r < t then q ⟨r, hr⟩ y else 0) else 0 := by
        simpa using (Fin.sum_univ_eq_sum_range
          (fun r : ℕ => if r < k then
            (if hr : r < t then q ⟨r, hr⟩ y else 0) else 0) t)
      _ = ∑ r ∈ Finset.range k, (if hr : r < t then q ⟨r, hr⟩ y else 0) := by
        have hs : (Finset.range t).filter (fun r => r < k) = Finset.range k := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
        rw [← Finset.sum_filter, hs]
  have hcol := h.column_prefix ⟨k, hk'⟩ y
  simpa [hsum] using hcol

private theorem finPrefixSum_eq_range {t m : ℕ} (hm : m ≤ t) (f : ℕ → ℝ) :
    (∑ j : Fin t, if j.val < m then f j.val else 0) =
      ∑ r ∈ Finset.range m, f r := by
  classical
  calc
    (∑ j : Fin t, if j.val < m then f j.val else 0) =
        ∑ r ∈ Finset.range t, if r < m then f r else 0 := by
      simpa using (Fin.sum_univ_eq_sum_range
        (fun r : ℕ => if r < m then f r else 0) t)
    _ = ∑ r ∈ Finset.range m, f r := by
      have hs : (Finset.range t).filter (fun r => r < m) = Finset.range m := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [← Finset.sum_filter, hs]

private theorem free_tracking_column_bound_pos {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (h : OrderedInput d t q) (x : Path t d) (m : ℕ) (hm : m ≤ t)
    (hmpos : 0 < m) (hRun : RunningThrough q x m) (y : Fin d) :
    (∑ r ∈ Finset.range m,
      if hr : r < t then if Free x r y then
        q ⟨r, hr⟩ y * trackingError q x r else 0 else 0) ≤
      2 * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
        (∑ j : Fin t, if j.val < m then trackingError q x j.val else 0) / d := by
  classical
  rcases hRun with ⟨hvalid, hstop⟩
  let E : ℕ → ℝ := fun r => trackingError q x (min r t)
  let I : ℕ → ℝ := fun r => if hr : r < t then if Free x r y then 1 else 0 else 0
  let Q : ℕ → ℝ := fun r => if hr : r < t then q ⟨r, hr⟩ y else 0
  let g : ℕ → ℝ := fun r => if hr : r < t then q ⟨r, hr⟩ y - 1 / d else 0
  let W : ℕ → ℝ := fun r => E r * I r
  have hE0 (r : ℕ) : 0 ≤ E r := trackingError_nonneg q x (min r t)
  have hEmono (r : ℕ) : E r ≤ E (r + 1) := by
    apply trackingError_mono q x
    exact min_le_min_right t (Nat.le_succ r)
  have hEbound (r : ℕ) (hr : r < m) : E r ≤ 1 / 20 := by
    have hrt : r < t := lt_of_lt_of_le hr hm
    simpa only [E, Nat.min_eq_left (Nat.le_of_lt hrt)] using hstop ⟨r, hrt⟩ hr
  have hI01 (r : ℕ) : I r = 0 ∨ I r = 1 := by
    dsimp [I]
    by_cases hrt : r < t
    · by_cases hf : Free x r y <;> simp [hrt, hf]
    · simp [hrt]
  have hImono (r : ℕ) : I (r + 1) ≤ I r := by
    by_cases hnext : r + 1 < t
    · have hcur : r < t := by omega
      by_cases hfnext : Free x (r + 1) y
      · have hfcur : Free x r y := Free_antitone x (Nat.le_succ r) y hfnext
        simp [I, hcur, hnext, hfcur, hfnext]
      · by_cases hfcur : Free x r y
        · simp [I, hcur, hnext, hfnext, hfcur]
        · simp [I, hcur, hnext, hfnext, hfcur]
    · by_cases hcur : r < t
      · by_cases hf : Free x r y <;> simp [I, hcur, hnext, hf]
      · simp [I, hcur, hnext]
  have hC : 0 ≤ (1 / 20 : ℝ) := by norm_num
  have hvariation :
      (∑ r ∈ Finset.range (m - 1), |W (r + 1) - W r|) ≤ 2 * (1 / 20 : ℝ) := by
    exact indicatorProduct_variation_bound m E I (1 / 20) hC hE0 hEmono hEbound
      hI01 hImono
  have hlast : m - 1 < m := Nat.sub_lt hmpos (by decide)
  have hIle (r : ℕ) : I r ≤ 1 := by
    rcases hI01 r with hzero | hone
    · simp [hzero]
    · simp [hone]
  have hIend_nonneg : 0 ≤ I (m - 1) := by
    rcases hI01 (m - 1) with hzero | hone
    · simp [hzero]
    · simp [hone]
  have hWnonneg : 0 ≤ W (m - 1) := mul_nonneg (hE0 _) hIend_nonneg
  have hWle : W (m - 1) ≤ 1 / 20 := by
    calc
      W (m - 1) = E (m - 1) * I (m - 1) := rfl
      _ ≤ E (m - 1) * 1 := mul_le_mul_of_nonneg_left (hIle (m - 1)) (hE0 _)
      _ ≤ 1 / 20 := by simpa using hEbound (m - 1) hlast
  have hWend : |W (m - 1)| ≤ 1 / 20 := by
    rw [abs_of_nonneg hWnonneg]
    exact hWle
  have hprefix (k : ℕ) (hk : k ≤ m) :
      |∑ r ∈ Finset.range k, g r| ≤ 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
    have hcol := orderedColumnRangeError q h k (le_trans hk hm) y
    have hident : (∑ r ∈ Finset.range k, g r) =
        (∑ r ∈ Finset.range k, Q r) - (k : ℝ) / d := by
      calc
        (∑ r ∈ Finset.range k, g r) =
            ∑ r ∈ Finset.range k, (Q r - 1 / d) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrt : r < t := lt_of_lt_of_le (Finset.mem_range.mp hr) (le_trans hk hm)
          simp [g, Q, hrt]
        _ = _ := by
          rw [Finset.sum_sub_distrib]
          simp [Finset.sum_const, Finset.card_range]
          ring
    rw [hident]
    exact hcol
  let ε : ℝ := 10 * (d : ℝ) ^ (-(1 / 8 : ℝ))
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have habel :
      |∑ r ∈ Finset.range m, W r * g r| ≤ (1 / 20 : ℝ) * ε +
        2 * (1 / 20 : ℝ) * ε := by
    exact sum_range_abel_bound m W g ε (1 / 20) (2 * (1 / 20)) hε hC
      (by positivity) hprefix hWend hvariation
  have hWsum : ∑ r ∈ Finset.range m, W r ≤ ∑ r ∈ Finset.range m, E r := by
    apply Finset.sum_le_sum
    intro r hr
    dsimp [W]
    simpa using mul_le_mul_of_nonneg_left (hIle r) (hE0 r)
  have hEsum : (∑ r ∈ Finset.range m, E r) =
      ∑ j : Fin t, if j.val < m then trackingError q x j.val else 0 := by
    calc
      (∑ r ∈ Finset.range m, E r) =
          ∑ r ∈ Finset.range m, trackingError q x r := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrt : r < t := lt_of_lt_of_le (Finset.mem_range.mp hr) hm
        simp only [E, Nat.min_eq_left (Nat.le_of_lt hrt)]
      _ = ∑ j : Fin t, if j.val < m then trackingError q x j.val else 0 := by
        symm
        exact finPrefixSum_eq_range hm (fun r => trackingError q x r)
  have htarget :
      (∑ r ∈ Finset.range m,
        if hr : r < t then if Free x r y then
          q ⟨r, hr⟩ y * trackingError q x r else 0 else 0) =
        ∑ r ∈ Finset.range m, W r * Q r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrt : r < t := lt_of_lt_of_le (Finset.mem_range.mp hr) hm
    have hEr : E r = trackingError q x r := by
      simp only [E, Nat.min_eq_left (Nat.le_of_lt hrt)]
    simp [W, Q, I, hrt, hEr]
    split_ifs <;> ring
  have hidentity :
      (∑ r ∈ Finset.range m, W r * Q r) =
        (∑ r ∈ Finset.range m, W r * g r) +
          (1 / d) * (∑ r ∈ Finset.range m, W r) := by
    calc
      (∑ r ∈ Finset.range m, W r * Q r) =
          ∑ r ∈ Finset.range m, W r * (g r + 1 / d) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrt : r < t := lt_of_lt_of_le (Finset.mem_range.mp hr) hm
        simp [Q, g, hrt]
      _ = (∑ r ∈ Finset.range m, W r * g r) +
          ∑ r ∈ Finset.range m, W r * (1 / d) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
      _ = (∑ r ∈ Finset.range m, W r * g r) +
          (1 / d) * (∑ r ∈ Finset.range m, W r) := by
        rw [← Finset.sum_mul]
        congr 1
        ring
  have hd : 0 < (d : ℝ) := by have := h.dimension; exact_mod_cast (by omega : 0 < d)
  have hWq :
      (∑ r ∈ Finset.range m, W r * Q r) ≤
        2 * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
          (1 / d) * (∑ j : Fin t, if j.val < m then trackingError q x j.val else 0) := by
    rw [hidentity]
    have hsumabs : (∑ r ∈ Finset.range m, W r * g r) ≤
        (1 / 20 : ℝ) * ε + 2 * (1 / 20 : ℝ) * ε := le_trans (le_abs_self _) habel
    have hWdiv : (1 / d) * (∑ r ∈ Finset.range m, W r) ≤
        (1 / d) * (∑ r ∈ Finset.range m, E r) :=
      mul_le_mul_of_nonneg_left hWsum (by positivity)
    rw [hEsum] at hWdiv
    have htheta : 0 ≤ (d : ℝ) ^ (-(1 / 8 : ℝ)) := by positivity
    dsimp [ε] at hsumabs
    nlinarith [hsumabs, hWdiv, htheta]
  rw [htarget]
  calc
    (∑ r ∈ Finset.range m, W r * Q r) ≤
        2 * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
          (1 / d) * (∑ j : Fin t, if j.val < m then trackingError q x j.val else 0) := hWq
    _ = 2 * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
          (∑ j : Fin t, if j.val < m then trackingError q x j.val else 0) / d := by ring

private theorem free_tracking_column_bound {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (h : OrderedInput d t q) (x : Path t d) (b : Fin (t + 1))
    (hRun : RunningThrough q x b.val) (y : Fin d) :
    (∑ r ∈ Finset.range b.val,
      if hr : r < t then if Free x r y then
        q ⟨r, hr⟩ y * trackingError q x r else 0 else 0) ≤
      2 * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
        (∑ j : Fin t, if j.val < b.val then trackingError q x j.val else 0) / d := by
  classical
  by_cases hb0 : b.val = 0
  · have hd : 0 < (d : ℝ) := by have := h.dimension; exact_mod_cast (by omega : 0 < d)
    simp [hb0]
    positivity
  · have hm : b.val ≤ t := by omega
    have hmpos : 0 < b.val := by omega
    have hrun : RunningThrough q x b.val := hRun
    simpa using free_tracking_column_bound_pos q h x b.val hm hmpos hrun y

/-- First summation by parts, TeX 03:673–680. -/
theorem drift_denominator_replacement : ∃ K : ℝ, 1 ≤ K ∧
    ∀ d t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ x a (b : Fin (t + 1)), RunningThrough q x b.val →
      |(∑ j : Fin t, if j.val < b.val then stepDrift q x a j else 0) -
        (∑ j : Fin t, if j.val < b.val then
          (∑ y, if Free x j.val y then q a y * q j y else 0) /
            (1 - (j.val : ℝ) / d) else 0)| ≤
        K * ((d : ℝ) ^ (-(1 / 8 : ℝ)) +
          (∑ j : Fin t, if j.val < b.val then trackingError q x j.val else 0) / d) := by
  classical
  refine ⟨40, by norm_num, ?_⟩
  intro d t q h x a b hRun
  have hd : 0 < (d : ℝ) := by have := h.dimension; exact_mod_cast (by omega : 0 < d)
  let m : ℕ := b.val
  have hm : m ≤ t := by dsimp [m]; omega
  rcases hRun with ⟨hprefix, hstop⟩
  have hvj (j : Fin t) (hj : j.val < m) : PrefixValid x j.val := by
    rcases hprefix with ⟨hvalid, hinj⟩
    refine ⟨?_, ?_⟩
    · intro k hk
      exact hvalid k (lt_trans hk hj)
    · intro i k hi hk heq
      exact hinj i k (lt_trans hi hj) (lt_trans hk hj) heq
  let N (j : Fin t) : ℝ :=
    ∑ y, if Free x j.val y then q a y * q j y else 0
  have hNnonneg (j : Fin t) : 0 ≤ N j := by
    unfold N
    apply Finset.sum_nonneg
    intro y hy
    split_ifs
    · exact mul_nonneg (h.nonneg a y) (h.nonneg j y)
    · norm_num
  have hstepBound (j : Fin t) (hj : j.val < m) :
      |stepDrift q x a j - N j / (1 - (j.val : ℝ) / d)| ≤
        20 * N j * trackingError q x j.val := by
    have hstopj := hstop j hj
    have hvalidj := hvj j hj
    have hmass := free_mass_before_stop q h x j hvalidj hstopj
    have hmassEq : availableMass q x j ∅ = 1 - usedMass q x j j.val := hmass.1
    have hD1 : 1 / 5 ≤ 1 - usedMass q x j j.val := by
      simpa [hmassEq] using hmass.2
    have hjt : (j.val : ℝ) ≤ (t : ℝ) := by exact_mod_cast j.isLt.le
    have hjbound : (j.val : ℝ) ≤ 3 * (d : ℝ) / 4 := le_trans hjt h.horizon
    have hjratio : (j.val : ℝ) / d ≤ 3 / 4 := by
      apply (div_le_iff₀ hd).2
      nlinarith [hjbound]
    have hD2 : 1 / 4 ≤ 1 - (j.val : ℝ) / d := by linarith
    have hUpos : 0 < 1 - usedMass q x j j.val := by linarith
    have hVpos : 0 < 1 - (j.val : ℝ) / d := by linarith
    have hdj : 0 < d - (j.val : ℝ) := by
      have hratio : (j.val : ℝ) / d < 1 := by linarith
      have hmul := (div_lt_iff₀ hd).1 hratio
      linarith
    have hden : (1 / 20 : ℝ) ≤
        (1 - usedMass q x j j.val) * (1 - (j.val : ℝ) / d) := by
      calc
        (1 / 20 : ℝ) = (1 / 5) * (1 / 4) := by norm_num
        _ ≤ (1 - usedMass q x j j.val) * (1 - (j.val : ℝ) / d) :=
          mul_le_mul hD1 hD2 (by norm_num) (by linarith)
    have hdenPos : 0 <
        (1 - usedMass q x j j.val) * (1 - (j.val : ℝ) / d) :=
      mul_pos hUpos hVpos
    have herr0 : 0 ≤ trackingError q x j.val := trackingError_nonneg q x j.val
    have herr : |usedMass q x j j.val - (j.val : ℝ) / d| ≤ trackingError q x j.val :=
      trackingError_ge_abs q x j.val j ⟨j.val, by omega⟩ (by rfl)
    have hformula : stepDrift q x a j =
        N j / (1 - usedMass q x j j.val) := by
      simpa [N] using (sequential_drift_increment q h x a j hvalidj hstopj).1
    have halgebra :
        N j / (1 - usedMass q x j j.val) - N j / (1 - (j.val : ℝ) / d) =
          N j * (usedMass q x j j.val - (j.val : ℝ) / d) /
            ((1 - usedMass q x j j.val) * (1 - (j.val : ℝ) / d)) := by
      field_simp [ne_of_gt hUpos, ne_of_gt hVpos, ne_of_gt hd, ne_of_gt hdj]
      <;> ring_nf
    have hnum :
        |N j * (usedMass q x j j.val - (j.val : ℝ) / d)| ≤
          N j * trackingError q x j.val := by
      calc
        _ = N j * |usedMass q x j j.val - (j.val : ℝ) / d| := by
          rw [abs_mul, abs_of_nonneg (hNnonneg j)]
        _ ≤ N j * trackingError q x j.val :=
          mul_le_mul_of_nonneg_left herr (hNnonneg j)
    have hquot :
        |N j * (usedMass q x j j.val - (j.val : ℝ) / d) /
          ((1 - usedMass q x j j.val) * (1 - (j.val : ℝ) / d))| ≤
          20 * N j * trackingError q x j.val := by
      rw [abs_div, abs_of_pos hdenPos]
      apply (div_le_iff₀ hdenPos).2
      calc
        |N j * (usedMass q x j j.val - (j.val : ℝ) / d)| ≤
            N j * trackingError q x j.val := hnum
        _ ≤ (20 * N j * trackingError q x j.val) *
              ((1 - usedMass q x j j.val) * (1 - (j.val : ℝ) / d)) := by
          have hne : 0 ≤ 20 * N j * trackingError q x j.val :=
            mul_nonneg (mul_nonneg (by norm_num) (hNnonneg j))
              (trackingError_nonneg q x j.val)
          calc
            N j * trackingError q x j.val =
                (20 * N j * trackingError q x j.val) * (1 / 20 : ℝ) := by ring
            _ ≤ (20 * N j * trackingError q x j.val) *
                ((1 - usedMass q x j j.val) * (1 - (j.val : ℝ) / d)) :=
              mul_le_mul_of_nonneg_left hden hne
    calc
      |stepDrift q x a j - N j / (1 - (j.val : ℝ) / d)| =
          |N j / (1 - usedMass q x j j.val) -
            N j / (1 - (j.val : ℝ) / d)| := by rw [hformula]
      _ = |N j * (usedMass q x j j.val - (j.val : ℝ) / d) /
            ((1 - usedMass q x j j.val) * (1 - (j.val : ℝ) / d))| := by rw [halgebra]
      _ ≤ 20 * N j * trackingError q x j.val := hquot
  let P : Fin t → ℝ := fun j => if j.val < m then stepDrift q x a j else 0
  let Q : Fin t → ℝ := fun j => if j.val < m then N j / (1 - (j.val : ℝ) / d) else 0
  have hsumdiff :
      (∑ j : Fin t, P j) - (∑ j : Fin t, Q j) =
      ∑ j : Fin t, if j.val < m then
        stepDrift q x a j - N j / (1 - (j.val : ℝ) / d) else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hlt : j.val < m <;> simp [P, Q, hlt]
  have hsumAbs :
      |∑ j : Fin t, if j.val < m then
        stepDrift q x a j - N j / (1 - (j.val : ℝ) / d) else 0| ≤
      20 * (∑ j : Fin t, if j.val < m then
        N j * trackingError q x j.val else 0) := by
    calc
      |∑ j : Fin t, if j.val < m then
          stepDrift q x a j - N j / (1 - (j.val : ℝ) / d) else 0| ≤
          ∑ j : Fin t,
            |if j.val < m then stepDrift q x a j -
              N j / (1 - (j.val : ℝ) / d) else 0| := by
        exact Finset.abs_sum_le_sum_abs
          (fun j : Fin t => if j.val < m then
            stepDrift q x a j - N j / (1 - (j.val : ℝ) / d) else 0) Finset.univ
      _ = ∑ j : Fin t, if j.val < m then
          |stepDrift q x a j - N j / (1 - (j.val : ℝ) / d)| else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hlt : j.val < m <;> simp [hlt]
      _ ≤ ∑ j : Fin t, if j.val < m then
          20 * N j * trackingError q x j.val else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hlt : j.val < m
        · simp only [if_pos hlt]
          exact hstepBound j hlt
        · simp [hlt]
      _ = 20 * (∑ j : Fin t, if j.val < m then
            N j * trackingError q x j.val else 0) := by
        calc
          _ = ∑ j : Fin t, 20 * (if j.val < m then
                N j * trackingError q x j.val else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            split_ifs <;> ring
          _ = _ := by rw [Finset.mul_sum]
  have haggregate :
      (∑ j : Fin t, if j.val < m then N j * trackingError q x j.val else 0) ≤
        2 * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
          (∑ j : Fin t, if j.val < m then trackingError q x j.val else 0) / d := by
    have hrowsum (j : Fin t) :
        N j * trackingError q x j.val =
          ∑ y : Fin d, q a y *
            (if Free x j.val y then q j y * trackingError q x j.val else 0) := by
      unfold N
      calc
        (∑ y : Fin d, if Free x j.val y then q a y * q j y else 0) *
            trackingError q x j.val =
          ∑ y : Fin d, (if Free x j.val y then q a y * q j y else 0) *
            trackingError q x j.val := by rw [Finset.sum_mul]
        _ = ∑ y : Fin d, q a y *
            (if Free x j.val y then q j y * trackingError q x j.val else 0) := by
          apply Finset.sum_congr rfl
          intro y hy
          split_ifs <;> ring
    have hswap :
        (∑ j : Fin t, if j.val < m then N j * trackingError q x j.val else 0) =
          ∑ y : Fin d, q a y *
            (∑ j : Fin t, if j.val < m then
              if Free x j.val y then q j y * trackingError q x j.val else 0 else 0) := by
      calc
        _ = ∑ j : Fin t, if j.val < m then
              ∑ y : Fin d, q a y *
                (if Free x j.val y then q j y * trackingError q x j.val else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hlt : j.val < m
          · simp [hlt, hrowsum]
          · simp [hlt]
        _ = ∑ j : Fin t, ∑ y : Fin d, if j.val < m then
              q a y * (if Free x j.val y then q j y * trackingError q x j.val else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hlt : j.val < m
          · simp [hlt]
          · simp [hlt]
        _ = ∑ y : Fin d, ∑ j : Fin t, if j.val < m then
              q a y * (if Free x j.val y then q j y * trackingError q x j.val else 0) else 0 :=
          Finset.sum_comm
        _ = ∑ y : Fin d, q a y *
              (∑ j : Fin t, if j.val < m then
                if Free x j.val y then q j y * trackingError q x j.val else 0 else 0) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          split_ifs <;> ring
    rw [hswap]
    have hinner (y : Fin d) :
        (∑ j : Fin t, if j.val < m then
          if Free x j.val y then q j y * trackingError q x j.val else 0 else 0) ≤
          2 * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
            (∑ j : Fin t, if j.val < m then trackingError q x j.val else 0) / d := by
      have hconvert :
          (∑ j : Fin t, if j.val < m then
            if Free x j.val y then q j y * trackingError q x j.val else 0 else 0) =
            ∑ r ∈ Finset.range m,
              if hr : r < t then if Free x r y then
                q ⟨r, hr⟩ y * trackingError q x r else 0 else 0 := by
        simpa using finPrefixSum_eq_range hm (fun r =>
          if hr : r < t then if Free x r y then
            q ⟨r, hr⟩ y * trackingError q x r else 0 else 0)
      rw [hconvert]
      simpa [m] using free_tracking_column_bound q h x b
        (by exact ⟨hprefix, hstop⟩) y
    have hBnd : 0 ≤ 2 * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
        (∑ j : Fin t, if j.val < m then trackingError q x j.val else 0) / d := by
      have hsum0 : 0 ≤ ∑ j : Fin t, if j.val < m then trackingError q x j.val else 0 := by
        apply Finset.sum_nonneg
        intro j hj
        split_ifs <;> simp [trackingError_nonneg]
      positivity
    calc
      (∑ y : Fin d, q a y *
          (∑ j : Fin t, if j.val < m then
            if Free x j.val y then q j y * trackingError q x j.val else 0 else 0)) ≤
          ∑ y : Fin d, q a y *
            (2 * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
              (∑ j : Fin t, if j.val < m then trackingError q x j.val else 0) / d) := by
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_left (hinner y) (h.nonneg a y)
      _ = 2 * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
            (∑ j : Fin t, if j.val < m then trackingError q x j.val else 0) / d := by
        rw [← Finset.sum_mul, h.row_sum a, one_mul]
  have htotal : |(∑ j : Fin t, if j.val < m then stepDrift q x a j else 0) -
      (∑ j : Fin t, if j.val < m then
        N j / (1 - (j.val : ℝ) / d) else 0)| ≤
      40 * ((d : ℝ) ^ (-(1 / 8 : ℝ)) +
        (∑ j : Fin t, if j.val < m then trackingError q x j.val else 0) / d) := by
    rw [hsumdiff]
    have hagg := haggregate
    have hnonneg : 0 ≤ (∑ j : Fin t,
        if j.val < m then trackingError q x j.val else 0) / d := by
      have hsum0 : 0 ≤ ∑ j : Fin t,
          if j.val < m then trackingError q x j.val else 0 := by
        apply Finset.sum_nonneg
        intro j hj
        split_ifs <;> simp [trackingError_nonneg]
      exact div_nonneg hsum0 (le_of_lt hd)
    nlinarith [hsumAbs, hagg, hnonneg,
      (show 0 ≤ (d : ℝ) ^ (-(1 / 8 : ℝ)) by positivity)]
  simpa [m, N] using htotal

private theorem reciprocal_free_column_bound_pos {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (h : OrderedInput d t q) (x : Path t d) (m : ℕ) (hm : m ≤ t)
    (hmpos : 0 < m) (y : Fin d) :
    |∑ j : Fin t, if j.val < m then if Free x j.val y then
      (q j y - 1 / d) / (1 - (j.val : ℝ) / d) else 0 else 0| ≤
      120 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
  classical
  let E : ℕ → ℝ := fun r => (1 - ((min r t : ℕ) : ℝ) / d)⁻¹
  let I : ℕ → ℝ := fun r => if hr : r < t then if Free x r y then 1 else 0 else 0
  let Q : ℕ → ℝ := fun r => if hr : r < t then q ⟨r, hr⟩ y else 0
  let g : ℕ → ℝ := fun r => if hr : r < t then q ⟨r, hr⟩ y - 1 / d else 0
  let W : ℕ → ℝ := fun r => E r * I r
  have hminfrac (r : ℕ) : ((min r t : ℕ) : ℝ) / d ≤ 3 / 4 := by
    have hmin : ((min r t : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast (Nat.min_le_right r t)
    apply (div_le_iff₀ (show 0 < (d : ℝ) from by
      have := h.dimension
      exact_mod_cast (by omega : 0 < d))).2
    have hbound : ((min r t : ℕ) : ℝ) ≤ 3 * (d : ℝ) / 4 := le_trans hmin h.horizon
    nlinarith [hbound]
  have hdenpos (r : ℕ) : 0 < 1 - ((min r t : ℕ) : ℝ) / d := by
    have := hminfrac r
    linarith
  have hdenlower (r : ℕ) :
      1 / 4 ≤ 1 - ((min r t : ℕ) : ℝ) / d := by linarith [hminfrac r]
  have hE0 (r : ℕ) : 0 ≤ E r := by
    unfold E
    exact inv_nonneg.mpr (le_of_lt (hdenpos r))
  have hEmono (r : ℕ) : E r ≤ E (r + 1) := by
    have hmin : ((min r t : ℕ) : ℝ) ≤ ((min (r + 1) t : ℕ) : ℝ) := by
      exact_mod_cast (min_le_min_right t (Nat.le_succ r))
    have hfrac : ((min r t : ℕ) : ℝ) / d ≤ ((min (r + 1) t : ℕ) : ℝ) / d :=
      (div_le_div_iff_of_pos_right
        (by have := h.dimension; exact_mod_cast (by omega : 0 < d))).2 hmin
    have hden : 1 - ((min (r + 1) t : ℕ) : ℝ) / d ≤
        1 - ((min r t : ℕ) : ℝ) / d := by linarith
    unfold E
    simpa [one_div] using one_div_le_one_div_of_le (hdenpos (r + 1)) hden
  have hEbound (r : ℕ) (hr : r < m) : E r ≤ 4 := by
    unfold E
    calc
      (1 - ((min r t : ℕ) : ℝ) / d)⁻¹ ≤ (1 / 4 : ℝ)⁻¹ :=
        by simpa [one_div] using one_div_le_one_div_of_le (by norm_num) (hdenlower r)
      _ = 4 := by norm_num
  have hI01 (r : ℕ) : I r = 0 ∨ I r = 1 := by
    dsimp [I]
    by_cases hrt : r < t
    · by_cases hf : Free x r y <;> simp [hrt, hf]
    · simp [hrt]
  have hImono (r : ℕ) : I (r + 1) ≤ I r := by
    by_cases hnext : r + 1 < t
    · have hcur : r < t := by omega
      by_cases hfnext : Free x (r + 1) y
      · have hfcur : Free x r y := Free_antitone x (Nat.le_succ r) y hfnext
        simp [I, hcur, hnext, hfcur, hfnext]
      · by_cases hfcur : Free x r y <;> simp [I, hcur, hnext, hfnext, hfcur]
    · by_cases hcur : r < t
      · by_cases hf : Free x r y <;> simp [I, hcur, hnext, hf]
      · simp [I, hcur, hnext]
  have hC : 0 ≤ (4 : ℝ) := by norm_num
  have hvariation :
      (∑ r ∈ Finset.range (m - 1), |W (r + 1) - W r|) ≤ 2 * (4 : ℝ) :=
    indicatorProduct_variation_bound m E I 4 hC hE0 hEmono hEbound hI01 hImono
  have hlast : m - 1 < m := Nat.sub_lt hmpos (by decide)
  have hIle (r : ℕ) : I r ≤ 1 := by
    rcases hI01 r with hzero | hone
    · simp [hzero]
    · simp [hone]
  have hIend : 0 ≤ I (m - 1) := by
    rcases hI01 (m - 1) with hzero | hone
    · simp [hzero]
    · simp [hone]
  have hWnonneg : 0 ≤ W (m - 1) := mul_nonneg (hE0 _) hIend
  have hWend : |W (m - 1)| ≤ 4 := by
    rw [abs_of_nonneg hWnonneg]
    calc
      W (m - 1) = E (m - 1) * I (m - 1) := rfl
      _ ≤ E (m - 1) * 1 := mul_le_mul_of_nonneg_left (hIle _) (hE0 _)
      _ ≤ 4 := by simpa using hEbound (m - 1) hlast
  have hprefix (k : ℕ) (hk : k ≤ m) :
      |∑ r ∈ Finset.range k, g r| ≤ 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
    have hcol := orderedColumnRangeError q h k (le_trans hk hm) y
    have hident : (∑ r ∈ Finset.range k, g r) =
        (∑ r ∈ Finset.range k, Q r) - (k : ℝ) / d := by
      calc
        (∑ r ∈ Finset.range k, g r) =
            ∑ r ∈ Finset.range k, (Q r - 1 / d) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrt : r < t := lt_of_lt_of_le (Finset.mem_range.mp hr) (le_trans hk hm)
          simp [g, Q, hrt]
        _ = (∑ r ∈ Finset.range k, Q r) -
              (∑ r ∈ Finset.range k, (1 / d : ℝ)) := by
          rw [Finset.sum_sub_distrib]
        _ = (∑ r ∈ Finset.range k, Q r) - (k : ℝ) / d := by
          simp [Finset.sum_const, Finset.card_range]
          ring
    rw [hident]
    exact hcol
  let ε : ℝ := 10 * (d : ℝ) ^ (-(1 / 8 : ℝ))
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have habel : |∑ r ∈ Finset.range m, W r * g r| ≤ 4 * ε + (2 * 4) * ε :=
    sum_range_abel_bound m W g ε 4 (2 * 4) hε hC (by positivity) hprefix hWend hvariation
  have htarget :
      (∑ j : Fin t, if j.val < m then if Free x j.val y then
        (q j y - 1 / d) / (1 - (j.val : ℝ) / d) else 0 else 0) =
        ∑ r ∈ Finset.range m, W r * g r := by
    have hconvert := finPrefixSum_eq_range hm (fun r : ℕ =>
      if hr : r < t then if Free x r y then
        (q ⟨r, hr⟩ y - 1 / d) / (1 - (r : ℝ) / d) else 0 else 0)
    calc
      (∑ j : Fin t, if j.val < m then if Free x j.val y then
          (q j y - 1 / d) / (1 - (j.val : ℝ) / d) else 0 else 0) =
          ∑ r ∈ Finset.range m, if hr : r < t then if Free x r y then
            (q ⟨r, hr⟩ y - 1 / d) / (1 - (r : ℝ) / d) else 0 else 0 := by
        simpa using hconvert
      _ = ∑ r ∈ Finset.range m, W r * g r := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrt : r < t := lt_of_lt_of_le (Finset.mem_range.mp hr) hm
        have hE : E r = (1 - (r : ℝ) / d)⁻¹ := by
          have hmin : min r t = r := Nat.min_eq_left (Nat.le_of_lt hrt)
          have hmin' : ((min r t : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast hmin
          dsimp [E]
          rw [hmin']
        by_cases hf : Free x r y
        · simp only [dif_pos hrt, if_pos hf]
          calc
            (q ⟨r, hrt⟩ y - 1 / d) / (1 - (r : ℝ) / d) =
                E r * (q ⟨r, hrt⟩ y - 1 / d) := by rw [hE]; ring
            _ = W r * g r := by simp [W, I, g, hrt, hf]
        · simp [W, I, g, hrt, hf]
  rw [htarget]
  have htheta : 0 ≤ (d : ℝ) ^ (-(1 / 8 : ℝ)) := by positivity
  dsimp [ε] at habel
  norm_num at habel ⊢
  nlinarith [habel, htheta]

/-- Second summation by parts, TeX 03:680–685. -/
theorem drift_column_replacement : ∃ K : ℝ, 1 ≤ K ∧
    ∀ d t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ x a (b : Fin (t + 1)), RunningThrough q x b.val →
      |(∑ j : Fin t, if j.val < b.val then
          (∑ y, if Free x j.val y then q a y * q j y else 0) /
            (1 - (j.val : ℝ) / d) else 0) -
        (∑ j : Fin t, if j.val < b.val then
          (1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) else 0) / d| ≤
        K * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
  classical
  refine ⟨120, by norm_num, ?_⟩
  intro d t q h x a b hRun
  have hd : 0 < (d : ℝ) := by
    have := h.dimension
    exact_mod_cast (by omega : 0 < d)
  let m := b.val
  have hm : m ≤ t := by dsimp [m]; omega
  have hvalid (j : Fin t) (hj : j.val < m) : PrefixValid x j.val := by
    rcases hRun with ⟨⟨hv, hi⟩, hs⟩
    refine ⟨?_, ?_⟩
    · intro k hk
      exact hv k (lt_trans hk hj)
    · intro i k hi' hk' heq
      exact hi i k (lt_trans hi' hj) (lt_trans hk' hj) heq
  let N (j : Fin t) : ℝ :=
    ∑ y, if Free x j.val y then q a y * q j y else 0
  have hleft :
      (∑ j : Fin t, if j.val < m then N j / (1 - (j.val : ℝ) / d) else 0) =
        ∑ y : Fin d, q a y *
          (∑ j : Fin t, if j.val < m then
            if Free x j.val y then q j y / (1 - (j.val : ℝ) / d) else 0 else 0) := by
    calc
      _ = ∑ j : Fin t, if j.val < m then
            ∑ y : Fin d, if Free x j.val y then
              q a y * (q j y / (1 - (j.val : ℝ) / d)) else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjm : j.val < m
        · simp only [if_pos hjm]
          unfold N
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro y hy
          split_ifs <;> ring
        · simp [hjm]
      _ = ∑ j : Fin t, ∑ y : Fin d, if j.val < m then
            if Free x j.val y then
              q a y * (q j y / (1 - (j.val : ℝ) / d)) else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjm : j.val < m <;> simp [hjm]
      _ = ∑ y : Fin d, ∑ j : Fin t, if j.val < m then
            if Free x j.val y then
              q a y * (q j y / (1 - (j.val : ℝ) / d)) else 0 else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> ring
  have hright :
      (∑ j : Fin t, if j.val < m then
          (1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) else 0) / d =
        ∑ y : Fin d, q a y *
          (∑ j : Fin t, if j.val < m then
            if Free x j.val y then (1 / d) / (1 - (j.val : ℝ) / d) else 0 else 0) := by
    have hmass (j : Fin t) (hj : j.val < m) :
        (∑ y : Fin d, if Free x j.val y then q a y else 0) =
          1 - usedMass q x a j.val :=
      free_row_mass_eq q a (h.row_sum a) x j (by have := h.dimension; omega) (hvalid j hj)
    calc
      _ = ∑ j : Fin t, if j.val < m then
          ((∑ y : Fin d, if Free x j.val y then q a y else 0) /
            (1 - (j.val : ℝ) / d)) / d else 0 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjm : j.val < m
        · simp only [if_pos hjm]
          rw [← hmass j hjm]
        · simp [hjm]
      _ = ∑ j : Fin t, if j.val < m then
          ∑ y : Fin d, if Free x j.val y then
            q a y * ((1 / d) / (1 - (j.val : ℝ) / d)) else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjm : j.val < m
        · simp only [if_pos hjm]
          rw [Finset.sum_div, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro y hy
          split_ifs <;> ring
        · simp [hjm]
      _ = ∑ j : Fin t, ∑ y : Fin d, if j.val < m then
          if Free x j.val y then
            q a y * ((1 / d) / (1 - (j.val : ℝ) / d)) else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjm : j.val < m <;> simp [hjm]
      _ = ∑ y : Fin d, ∑ j : Fin t, if j.val < m then
          if Free x j.val y then
            q a y * ((1 / d) / (1 - (j.val : ℝ) / d)) else 0 else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> ring
  have hdiff :
      (∑ j : Fin t, if j.val < m then N j / (1 - (j.val : ℝ) / d) else 0) -
        (∑ j : Fin t, if j.val < m then
          (1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) else 0) / d =
        ∑ y : Fin d, q a y *
          (∑ j : Fin t, if j.val < m then if Free x j.val y then
            (q j y - 1 / d) / (1 - (j.val : ℝ) / d) else 0 else 0) := by
    rw [hleft, hright]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjm : j.val < m
    · simp only [if_pos hjm]
      split_ifs <;> ring
    · simp [hjm]
  have hbound :
      |∑ y : Fin d, q a y *
          (∑ j : Fin t, if j.val < m then if Free x j.val y then
            (q j y - 1 / d) / (1 - (j.val : ℝ) / d) else 0 else 0)| ≤
        120 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
    calc
      _ ≤ ∑ y : Fin d, |q a y *
          (∑ j : Fin t, if j.val < m then if Free x j.val y then
            (q j y - 1 / d) / (1 - (j.val : ℝ) / d) else 0 else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y : Fin d, q a y * |∑ j : Fin t, if j.val < m then
            if Free x j.val y then
              (q j y - 1 / d) / (1 - (j.val : ℝ) / d) else 0 else 0| := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [abs_mul, abs_of_nonneg (h.nonneg a y)]
      _ ≤ ∑ y : Fin d, q a y * (120 * (d : ℝ) ^ (-(1 / 8 : ℝ))) := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases hmpos : 0 < m
        · exact mul_le_mul_of_nonneg_left
            (reciprocal_free_column_bound_pos q h x m hm hmpos y) (h.nonneg a y)
        · have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmpos
          simp [hmzero]
          exact mul_nonneg (h.nonneg a y)
            (mul_nonneg (by norm_num) (by positivity))
      _ = 120 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
        rw [← Finset.sum_mul, h.row_sum a, one_mul]
  rw [hdiff]
  exact hbound

/-- TeX 03:687–689, including the first potential stopping index. -/
def DriftRecurrence {d t : ℕ} (q : Fin t → Fin d → ℝ) (K : ℝ) : Prop :=
  ∀ x (b : Fin (t + 1)), RunningThrough q x b.val → MartingaleGood q x →
    trackingError q x b.val ≤ K * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
      K / d * ∑ j : Fin t, if j.val < b.val then trackingError q x j.val else 0

theorem tracking_drift_recurrence : ∃ K : ℝ, 1 ≤ K ∧
    ∀ d t (q : Fin t → Fin d → ℝ), OrderedInput d t q → DriftRecurrence q K := by
  classical
  obtain ⟨Kden, hKden, hdenLemma⟩ := drift_denominator_replacement
  obtain ⟨Kcol, hKcol, hcolLemma⟩ := drift_column_replacement
  let Ktot : ℝ := Kden + Kcol + 10
  refine ⟨Ktot, by dsimp [Ktot]; linarith, ?_⟩
  intro d t q h x b hRun hMG
  rcases hRun with ⟨hprefix, hstop⟩
  have hd : 0 < (d : ℝ) := by
    have := h.dimension
    exact_mod_cast (by omega : 0 < d)
  let θ : ℝ := (d : ℝ) ^ (-(1 / 8 : ℝ))
  let S (k : ℕ) : ℝ :=
    ∑ j : Fin t, if j.val < k then trackingError q x j.val else 0
  have hprefixValid (k : ℕ) (hk : k ≤ b.val) : PrefixValid x k := by
    rcases hprefix with ⟨hv, hi⟩
    refine ⟨?_, ?_⟩
    · intro j hj
      exact hv j (lt_of_lt_of_le hj hk)
    · intro i j hi' hj' heq
      exact hi i j (lt_of_lt_of_le hi' hk) (lt_of_lt_of_le hj' hk) heq
  have hrun (k : Fin (t + 1)) (hk : k.val ≤ b.val) :
      RunningThrough q x k.val := by
    constructor
    · exact hprefixValid k.val hk
    · intro j hj
      exact hstop j (lt_of_lt_of_le hj hk)
  have hbase (a : Fin t) (k : Fin (t + 1)) (hk : k.val ≤ b.val) :
      |(∑ j : Fin t, if j.val < k.val then
          (1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) else 0) / d -
        (k.val : ℝ) / d| ≤ 4 * S k.val / d := by
    let T (j : Fin t) : ℝ :=
      if j.val < k.val then
        (1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) / d - 1 / d else 0
    have hconst :
        (∑ j : Fin t, if j.val < k.val then (1 / d : ℝ) else 0) =
          (k.val : ℝ) / d := by
      have hrange := finPrefixSum_eq_range (by omega : k.val ≤ t)
        (fun _ : ℕ => (1 / d : ℝ))
      calc
        _ = (k.val : ℝ) * (1 / d) := by
          simpa [Finset.sum_const, Finset.card_range] using hrange
        _ = (k.val : ℝ) / d := by ring
    have hident :
        (∑ j : Fin t, if j.val < k.val then
            (1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) else 0) / d -
          (k.val : ℝ) / d = ∑ j : Fin t, T j := by
      rw [← hconst, Finset.sum_div]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjk : j.val < k.val <;> simp [T, hjk]
    have hterm (j : Fin t) (hjk : j.val < k.val) :
        |(1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) / d - 1 / d| ≤
          4 * trackingError q x j.val / d := by
      have hjreal : (j.val : ℝ) ≤ (t : ℝ) := by exact_mod_cast j.isLt.le
      have hjbound : (j.val : ℝ) ≤ 3 * (d : ℝ) / 4 := le_trans hjreal h.horizon
      have hjratio : (j.val : ℝ) / d ≤ 3 / 4 := by
        apply (div_le_iff₀ hd).2
        nlinarith [hjbound]
      have hden : (1 / 4 : ℝ) ≤ 1 - (j.val : ℝ) / d := by linarith
      have hdenpos : 0 < 1 - (j.val : ℝ) / d := by linarith
      have hgap : 0 < d - (j.val : ℝ) := by
        have hratio : (j.val : ℝ) / d < 1 := by linarith
        have hmul := (div_lt_iff₀ hd).1 hratio
        linarith
      have hprodpos : 0 < (1 - (j.val : ℝ) / d) * d := mul_pos hdenpos hd
      have hprod : d / 4 ≤ (1 - (j.val : ℝ) / d) * d := by
        nlinarith [mul_le_mul_of_nonneg_right hden (le_of_lt hd)]
      have herr :
          |usedMass q x a j.val - (j.val : ℝ) / d| ≤ trackingError q x j.val :=
        trackingError_ge_abs q x j.val a ⟨j.val, by omega⟩ (by rfl)
      have herr0 : 0 ≤ trackingError q x j.val := trackingError_nonneg q x j.val
      have halg :
          (1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) / d - 1 / d =
            ((j.val : ℝ) / d - usedMass q x a j.val) /
              ((1 - (j.val : ℝ) / d) * d) := by
        field_simp [ne_of_gt hdenpos, ne_of_gt hd, ne_of_gt hgap]
        <;> ring
      rw [halg, abs_div, abs_of_pos hprodpos]
      calc
        |(j.val : ℝ) / d - usedMass q x a j.val| /
            ((1 - (j.val : ℝ) / d) * d) =
            |usedMass q x a j.val - (j.val : ℝ) / d| /
              ((1 - (j.val : ℝ) / d) * d) := by
          congr 1
          rw [abs_sub_comm]
        _ ≤ trackingError q x j.val / ((1 - (j.val : ℝ) / d) * d) :=
          div_le_div_of_nonneg_right herr (le_of_lt hprodpos)
        _ ≤ trackingError q x j.val / (d / 4) :=
          div_le_div_of_nonneg_left herr0 (by positivity) hprod
        _ = 4 * trackingError q x j.val / d := by
          field_simp [ne_of_gt hd]
          <;> ring
    have habs : |∑ j : Fin t, T j| ≤ ∑ j : Fin t, |T j| :=
      Finset.abs_sum_le_sum_abs T Finset.univ
    have hsum :
        (∑ j : Fin t, |T j|) ≤ 4 * S k.val / d := by
      calc
        _ ≤ ∑ j : Fin t, if j.val < k.val then
            4 * trackingError q x j.val / d else 0 := by
          apply Finset.sum_le_sum
          intro j hj
          by_cases hjk : j.val < k.val
          · simp only [if_pos hjk]
            simpa [T, hjk] using hterm j hjk
          · simp [T, hjk]
        _ = 4 * S k.val / d := by
          calc
            _ = (∑ j : Fin t, if j.val < k.val then
                4 * trackingError q x j.val else 0) / d := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro j hj
              split_ifs <;> ring
            _ = 4 * S k.val / d := by
              congr 1
              dsimp [S]
              calc
                (∑ j : Fin t, if j.val < k.val then
                    4 * trackingError q x j.val else 0) =
                  ∑ j : Fin t, 4 * (if j.val < k.val then
                    trackingError q x j.val else 0) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    split_ifs <;> ring
                _ = _ := by rw [Finset.mul_sum]
    rw [hident]
    exact habs.trans hsum
  have hdrift (a : Fin t) (k : Fin (t + 1)) (hk : k.val ≤ b.val) :
      |(∑ j : Fin t, if j.val < k.val then stepDrift q x a j else 0) -
          (k.val : ℝ) / d| ≤
        (Kden + Kcol + 1) * θ + (Kden + 4) * (S k.val / d) := by
    let hkRun := hrun k hk
    have hden := hdenLemma d t q h x a k hkRun
    have hcol := hcolLemma d t q h x a k hkRun
    have hbase' := hbase a k hk
    have htheta : (d : ℝ) ^ (-(1 / 8 : ℝ)) = θ := by rfl
    have hsumErr :
        (∑ j : Fin t, if j.val < k.val then trackingError q x j.val else 0) = S k.val := by rfl
    have hden' :
        |(∑ j : Fin t, if j.val < k.val then stepDrift q x a j else 0) -
            (∑ j : Fin t, if j.val < k.val then
              (∑ y, if Free x j.val y then q a y * q j y else 0) /
                (1 - (j.val : ℝ) / d) else 0)| ≤
          Kden * (θ + S k.val / d) := by
      simpa [θ, S, one_div] using hden
    have hcol' :
        |(∑ j : Fin t, if j.val < k.val then
            (∑ y, if Free x j.val y then q a y * q j y else 0) /
              (1 - (j.val : ℝ) / d) else 0) -
          (∑ j : Fin t, if j.val < k.val then
            (1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) else 0) / d| ≤
          Kcol * θ := by
      simpa [θ] using hcol
    have hsumid :
        ((∑ j : Fin t, if j.val < k.val then stepDrift q x a j else 0) -
          (k.val : ℝ) / d) =
        ((∑ j : Fin t, if j.val < k.val then stepDrift q x a j else 0) -
          (∑ j : Fin t, if j.val < k.val then
            (∑ y, if Free x j.val y then q a y * q j y else 0) /
              (1 - (j.val : ℝ) / d) else 0)) +
        ((∑ j : Fin t, if j.val < k.val then
            (∑ y, if Free x j.val y then q a y * q j y else 0) /
              (1 - (j.val : ℝ) / d) else 0) -
          (∑ j : Fin t, if j.val < k.val then
            (1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) else 0) / d) +
        ((∑ j : Fin t, if j.val < k.val then
            (1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) else 0) / d -
          (k.val : ℝ) / d) := by ring
    rw [hsumid]
    let hA := (∑ j : Fin t, if j.val < k.val then stepDrift q x a j else 0) -
      (∑ j : Fin t, if j.val < k.val then
        (∑ y, if Free x j.val y then q a y * q j y else 0) /
          (1 - (j.val : ℝ) / d) else 0)
    let hB := (∑ j : Fin t, if j.val < k.val then
        (∑ y, if Free x j.val y then q a y * q j y else 0) /
          (1 - (j.val : ℝ) / d) else 0) -
      (∑ j : Fin t, if j.val < k.val then
        (1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) else 0) / d
    let hC := (∑ j : Fin t, if j.val < k.val then
        (1 - usedMass q x a j.val) / (1 - (j.val : ℝ) / d) else 0) / d -
      (k.val : ℝ) / d
    have hsumAbs : |hA + hB + hC| ≤ |hA| + |hB| + |hC| := by
      calc
        |hA + hB + hC| ≤ |hA + hB| + |hC| := abs_add_le _ _
        _ ≤ |hA| + |hB| + |hC| :=
          add_le_add (abs_add_le hA hB) (le_refl (|hC|))
    have hupper :
        |hA| + |hB| + |hC| ≤
          (Kden * (θ + S k.val / d) + Kcol * θ) + 4 * S k.val / d := by
      have hbaseC : |hC| ≤ 4 * S k.val / d := by
        simpa [hC] using hbase'
      exact add_le_add (add_le_add hden' hcol') hbaseC
    have hfinal :
        |hA + hB + hC| ≤
          (Kden + Kcol + 1) * θ + (Kden + 4) * (S k.val / d) := by
      calc
        _ ≤ |hA| + |hB| + |hC| := hsumAbs
        _ ≤ (Kden * (θ + S k.val / d) + Kcol * θ) +
            4 * S k.val / d := hupper
        _ = (Kden + Kcol) * θ + (Kden + 4) * (S k.val / d) := by ring
        _ ≤ (Kden + Kcol + 1) * θ + (Kden + 4) * (S k.val / d) := by
          have htheta0 : 0 ≤ θ := by dsimp [θ]; positivity
          have hcoef : Kden + Kcol ≤ Kden + Kcol + 1 := by linarith
          exact add_le_add
            (mul_le_mul_of_nonneg_right hcoef htheta0) (le_refl _)
    simpa [hA, hB, hC] using hfinal
  have hmax :
      ∀ a : Fin t, ∀ k : Fin (t + 1), k.val ≤ b.val →
        |usedMass q x a k.val - (k.val : ℝ) / d| ≤
          Ktot * θ + Ktot / d * S b.val := by
    intro a k hk
    have hrunK := hrun k hk
    have hmg := hMG a k
    have hmg' : |martingalePart q x a k.val| ≤ θ := by simpa [θ] using hmg
    have hsumid :
        usedMass q x a k.val - (k.val : ℝ) / d =
          martingalePart q x a k.val +
            ((∑ j : Fin t, if j.val < k.val then stepDrift q x a j else 0) -
              (k.val : ℝ) / d) := by
      have hconst :
          (∑ j : Fin t, if j.val < k.val then (1 / d : ℝ) else 0) =
            (k.val : ℝ) / d := by
        have hrange := finPrefixSum_eq_range (by omega : k.val ≤ t)
          (fun _ : ℕ => (1 / d : ℝ))
        calc
          _ = (k.val : ℝ) * (1 / d) := by
            simpa [Finset.sum_const, Finset.card_range] using hrange
          _ = (k.val : ℝ) / d := by ring
      calc
        usedMass q x a k.val - (k.val : ℝ) / d =
            (∑ j : Fin t, if j.val < k.val then (x j).elim 0 (q a) else 0) -
              (∑ j : Fin t, if j.val < k.val then (1 / d : ℝ) else 0) := by
          rw [show usedMass q x a k.val =
            ∑ j : Fin t, if j.val < k.val then (x j).elim 0 (q a) else 0 by rfl, hconst]
        _ = ∑ j : Fin t, if j.val < k.val then
              (x j).elim 0 (q a) - 1 / d else 0 := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          split_ifs <;> ring
        _ = ∑ j : Fin t, if j.val < k.val then
              ((x j).elim 0 (q a) - stepDrift q x a j) +
                (stepDrift q x a j - 1 / d) else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          split_ifs <;> ring
        _ = (∑ j : Fin t, if j.val < k.val then
              (x j).elim 0 (q a) - stepDrift q x a j else 0) +
              ∑ j : Fin t, if j.val < k.val then
                stepDrift q x a j - 1 / d else 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hjk : j.val < k.val <;> simp [hjk] <;> ring
        _ = martingalePart q x a k.val +
              ((∑ j : Fin t, if j.val < k.val then stepDrift q x a j else 0) -
                (k.val : ℝ) / d) := by
          have hdriftSum :
              (∑ j : Fin t, if j.val < k.val then stepDrift q x a j else 0) -
            (k.val : ℝ) / d =
              ∑ j : Fin t, if j.val < k.val then stepDrift q x a j - 1 / d else 0 := by
            rw [← hconst, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hjk : j.val < k.val <;> simp [hjk] <;> ring
          rw [show (∑ j : Fin t, if j.val < k.val then
            (x j).elim 0 (q a) - stepDrift q x a j else 0) =
              martingalePart q x a k.val by rfl, hdriftSum]
    have hsumErrMono : S k.val ≤ S b.val := by
      dsimp [S]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hjk : j.val < k.val
      · have hjb : j.val < b.val := lt_of_lt_of_le hjk hk
        simp [hjk, hjb]
      · by_cases hjb : j.val < b.val
        · simp [hjk, hjb, trackingError_nonneg]
        · simp [hjk, hjb]
    have herror :
        |usedMass q x a k.val - (k.val : ℝ) / d| ≤
          θ + (Kden + Kcol + 1) * θ + (Kden + 4) * (S k.val / d) := by
      rw [hsumid]
      have hmart := abs_add_le (martingalePart q x a k.val)
        ((∑ j : Fin t, if j.val < k.val then stepDrift q x a j else 0) -
          (k.val : ℝ) / d)
      nlinarith [hmg', hdrift a k hk]
    have hnonnegS : 0 ≤ S k.val := by
      dsimp [S]
      apply Finset.sum_nonneg
      intro j hj
      by_cases hjk : j.val < k.val
      · simpa [hjk] using trackingError_nonneg q x j.val
      · simp [hjk]
    have hmonoBound : S k.val / d ≤ S b.val / d :=
      div_le_div_of_nonneg_right hsumErrMono (le_of_lt hd)
    have hSnonneg : 0 ≤ S b.val := by
      dsimp [S]
      apply Finset.sum_nonneg
      intro j hj
      by_cases hjb : j.val < b.val
      · simpa [hjb] using trackingError_nonneg q x j.val
      · simp [hjb]
    have htheta0 : 0 ≤ θ := by dsimp [θ]; positivity
    have hKcoef : Kden + 4 ≤ Ktot := by dsimp [Ktot]; linarith [hKcol]
    have hKtheta : Kden + Kcol + 2 ≤ Ktot := by dsimp [Ktot]; linarith
    have hK :
        θ + (Kden + Kcol + 1) * θ + (Kden + 4) * (S k.val / d) ≤
          Ktot * θ + Ktot / d * S b.val := by
      have hthetaBound := mul_le_mul_of_nonneg_right hKtheta htheta0
      have hscale := mul_le_mul_of_nonneg_left hmonoBound
        (show 0 ≤ Kden + 4 by linarith [hKden])
      have hSbound :
          (Kden + 4) * (S b.val / d) ≤ Ktot / d * S b.val := by
        calc
          _ ≤ Ktot * (S b.val / d) := mul_le_mul_of_nonneg_right hKcoef
            (div_nonneg hSnonneg (le_of_lt hd))
          _ = Ktot / d * S b.val := by ring
      calc
        _ = (Kden + Kcol + 2) * θ + (Kden + 4) * (S k.val / d) := by ring
        _ ≤ Ktot * θ + (Kden + 4) * (S b.val / d) := add_le_add hthetaBound hscale
        _ ≤ _ := add_le_add_right hSbound (Ktot * θ)
    exact herror.trans hK
  conv_lhs => rw [trackingError]
  refine csSup_le ⟨0, Or.inl rfl⟩ ?_
  intro r hr
  rcases hr with hzero | ⟨a, k, hk, rfl⟩
  · subst r
    have hS0 : 0 ≤ S b.val := by
      dsimp [S]
      apply Finset.sum_nonneg
      intro j hj
      by_cases hjb : j.val < b.val
      · simpa [hjb] using trackingError_nonneg q x j.val
      · simp [hjb]
    have htheta0 : 0 ≤ θ := by dsimp [θ]; positivity
    positivity
  · have hk' : k.val ≤ b.val := hk
    simpa [θ, S] using hmax a k hk'

/-- Scalar iteration isolated from the stochastic model, TeX 03:691. -/
theorem discrete_tracking_gronwall (n : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (e : Fin (n + 1) → ℝ) (hn : ∀ b, 0 ≤ e b)
    (hr : ∀ b, e b ≤ A + B * ∑ j : Fin (n + 1), if j.val < b.val then e j else 0) :
    ∀ b, e b ≤ A * Real.exp (B * b.val) := by
  classical
  let enat : ℕ → ℝ := fun r => if hr : r < n + 1 then e ⟨r, hr⟩ else 0
  let S : ℕ → ℝ := fun m => ∑ r ∈ Finset.range m, enat r
  let u : ℕ → ℝ := fun m => A + B * S m
  have hprefix (m : ℕ) (hm : m ≤ n + 1) :
      (∑ j : Fin (n + 1), if j.val < m then e j else 0) = S m := by
    have hval (j : Fin (n + 1)) : enat j.val = e j := by
      dsimp [enat]
      rw [if_pos j.isLt]
    calc
      (∑ j : Fin (n + 1), if j.val < m then e j else 0) =
          ∑ j : Fin (n + 1), if j.val < m then enat j.val else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [hval j]
      _ = ∑ r ∈ Finset.range (n + 1), if r < m then enat r else 0 := by
        simpa using (Fin.sum_univ_eq_sum_range
          (fun r : ℕ => if r < m then enat r else 0) (n + 1))
      _ = S m := by
        dsimp [S]
        have hs : (Finset.range (n + 1)).filter (fun r => r < m) = Finset.range m := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
        rw [← Finset.sum_filter, hs]
  have hSsucc (m : ℕ) (hm : m ≤ n) :
      S (m + 1) = S m + e ⟨m, by omega⟩ := by
    dsimp [S]
    rw [Finset.sum_range_succ]
    simp [enat, hm]
  have huBound : ∀ m : ℕ, m ≤ n + 1 → u m ≤ A * Real.exp (B * (m : ℝ)) := by
    intro m
    induction m with
    | zero =>
        intro hm
        simp [u, S]
    | succ m ih =>
        intro hm
        have hmle : m ≤ n := by omega
        have hprev := ih (by omega)
        have hb := hr ⟨m, by omega⟩
        rw [hprefix m (by omega)] at hb
        have hem : e ⟨m, by omega⟩ ≤ u m := by
          dsimp [u]
          exact hb
        have huStep : u (m + 1) = u m + B * e ⟨m, by omega⟩ := by
          dsimp [u]
          rw [hSsucc m hmle]
          ring
        have hbase : 1 + B ≤ Real.exp B := by
          simpa [add_comm] using Real.add_one_le_exp B
        calc
          u (m + 1) = u m + B * e ⟨m, by omega⟩ := huStep
          _ ≤ u m + B * u m := by gcongr
          _ = (1 + B) * u m := by ring
          _ ≤ (1 + B) * (A * Real.exp (B * (m : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hprev (by positivity)
          _ ≤ Real.exp B * (A * Real.exp (B * (m : ℝ))) :=
            mul_le_mul_of_nonneg_right hbase (by positivity)
          _ = A * Real.exp (B * ((m + 1 : ℕ) : ℝ)) := by
            have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
            calc
              Real.exp B * (A * Real.exp (B * (m : ℝ))) =
                  A * (Real.exp (B * (m : ℝ)) * Real.exp B) := by ring
              _ = A * Real.exp (B * (m : ℝ) + B) := by rw [Real.exp_add]
              _ = A * Real.exp (B * ((m + 1 : ℕ) : ℝ)) := by
                apply congrArg (fun r : ℝ => A * Real.exp r)
                rw [hcast]
                ring
  intro b
  have hbRec := hr b
  rw [hprefix b.val (Nat.le_of_lt b.isLt)] at hbRec
  have hbe : e b ≤ u b.val := by
    dsimp [u]
    exact hbRec
  exact hbe.trans (huBound b.val (Nat.le_of_lt b.isLt))

/-- TeX 03:691–693: bootstrap the recurrence through a possible stop. -/
theorem tracking_bootstrap (K : ℝ) (hK : 1 ≤ K) :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      DriftRecurrence q K → ∀ x, sequentialWeight q x ≠ 0 → MartingaleGood q x → Good q x := by
  sorry

/-- Finite event transfer; avoids asserting that zero-weight paths are valid. -/
theorem tracking_probability_transfer {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (h : OrderedInput d t q)
    (hc : 1 - failureBound d ≤ (sequentialLaw q h.nonneg h.row_sum).pr (MartingaleGood q))
    (hb : ∀ x, sequentialWeight q x ≠ 0 → MartingaleGood q x → Good q x) :
    1 - failureBound d ≤ (sequentialLaw q h.nonneg h.row_sum).pr (Good q) := by
  classical
  let P := sequentialLaw q h.nonneg h.row_sum
  have hmono : P.pr (MartingaleGood q) ≤ P.pr (Good q) := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro x hx
    by_cases hm : MartingaleGood q x
    · by_cases hg : Good q x
      · simp [hm, hg]
      · have hw : sequentialWeight q x = 0 := by
          by_contra hne
          exact hg (hb x hne hm)
        simp only [if_pos hm, if_neg hg]
        have hpw : P.w x = 0 := by simpa [P, sequentialLaw] using hw
        simp only [hpw]
        exact le_rfl
    · simp only [if_neg hm]
      by_cases hg : Good q x
      · simp [hg, P.nonneg x]
      · simp [hg]
  have := hc.trans hmono
  simpa [P] using this

end HypercubeRamsey.Injection
