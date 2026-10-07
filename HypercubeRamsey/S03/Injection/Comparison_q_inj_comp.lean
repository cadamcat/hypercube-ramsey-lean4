import HypercubeRamsey.S03.Injection.Sampler
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.Tools.Concentration

set_option maxHeartbeats 0

/-!
Private finite-kernel helpers for the q-inj-comp lane.
-/

namespace HypercubeRamsey.Lane_q_inj_comp

open HypercubeRamsey.Injection
open scoped BigOperators
open Classical

def takePrefix {α : Type*} {n m : ℕ} (hm : m ≤ n) (x : Fin n → α) : Fin m → α :=
  fun i => x ⟨i.val, lt_of_lt_of_le i.isLt hm⟩

def appendLast {α : Type*} {n : ℕ} (h : Fin n → α) (z : α) :
    Fin (n + 1) → α :=
  fun i => if hi : i.val < n then h ⟨i.val, hi⟩ else z

def lastValue {α : Type*} {n : ℕ} (x : Fin (n + 1) → α) : α :=
  x ⟨n, Nat.lt_succ_self n⟩

private theorem takePrefix_appendLast {α : Type*} {n : ℕ}
    (h : Fin n → α) (z : α) :
    takePrefix (Nat.le_succ n) (appendLast h z) = h := by
  funext i
  simp [takePrefix, appendLast]

private theorem lastValue_appendLast {α : Type*} {n : ℕ}
    (h : Fin n → α) (z : α) : lastValue (appendLast h z) = z := by
  simp [lastValue, appendLast]

private theorem appendLast_takePrefix_lastValue {α : Type*} {n : ℕ}
    (x : Fin (n + 1) → α) :
    appendLast (takePrefix (Nat.le_succ n) x) (lastValue x) = x := by
  funext i
  by_cases hi : i.val < n
  · simp [appendLast, takePrefix, hi]
  · have hi' : i.val = n := by omega
    have heq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hi'
    subst i
    simp [appendLast, lastValue]

def pathFromPrefix {d t : ℕ} (j : Fin t)
    (h : Fin j.val → Option (Fin d)) : Injection.Path t d :=
  fun k => if hk : k.val < j.val then h ⟨k.val, hk⟩ else none

private theorem usedMass_prefix_congr {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x x' : Injection.Path t d) (j : Fin t)
    (hprev : ∀ k : Fin t, k.val < j.val → x k = x' k)
    (a : Fin t) (k : Fin (t + 1)) (hk : k.val ≤ j.val) :
    usedMass q x a k.val = usedMass q x' a k.val := by
  classical
  unfold usedMass
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hlt : l.val < k.val
  · simp [hlt, hprev l (lt_of_lt_of_le hlt hk)]
  · simp [hlt]

private theorem trackingError_prefix_congr {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (x x' : Injection.Path t d) (j : Fin t)
    (hprev : ∀ k : Fin t, k.val < j.val → x k = x' k) :
    trackingError q x j.val = trackingError q x' j.val := by
  classical
  unfold trackingError
  congr 1
  ext r
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro (hr0 | ⟨a, k, hk, hr⟩)
    · exact Or.inl hr0
    · refine Or.inr ⟨a, k, hk, ?_⟩
      rw [usedMass_prefix_congr q x x' j hprev a k hk] at hr
      exact hr
  · rintro (hr0 | ⟨a, k, hk, hr⟩)
    · exact Or.inl hr0
    · refine Or.inr ⟨a, k, hk, ?_⟩
      rw [usedMass_prefix_congr q x' x j (fun k hk => (hprev k hk).symm) a k hk] at hr
      exact hr

private theorem forcingStepWeight_prefix_congr {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (S : Finset (Fin t)) (y : Fin t → Fin d)
    (x x' : Injection.Path t d) (j : Fin t) (z : Option (Fin d))
    (hprev : ∀ k : Fin t, k.val < j.val → x k = x' k) :
    forcingStepWeight q S y x j z = forcingStepWeight q S y x' j z := by
  classical
  have hvalid : PrefixValid x j.val = PrefixValid x' j.val := by
    apply propext
    constructor
    · rintro ⟨hvalid, hinj⟩
      refine ⟨?_, ?_⟩
      · intro k hk
        rw [← hprev k hk]
        exact hvalid k hk
      · intro k l hk hl heq
        have heq' : x k = x l := by
          rw [hprev k hk, hprev l hl]
          exact heq
        exact hinj k l hk hl heq'
    · rintro ⟨hvalid, hinj⟩
      refine ⟨?_, ?_⟩
      · intro k hk
        rw [hprev k hk]
        exact hvalid k hk
      · intro k l hk hl heq
        have heq' : x' k = x' l := by
          rw [← hprev k hk, ← hprev l hl]
          exact heq
        exact hinj k l hk hl heq'
  have htrack : trackingError q x j.val = trackingError q x' j.val :=
    trackingError_prefix_congr q x x' j hprev
  have hfree (v : Fin d) : Free x j.val v = Free x' j.val v := by
    apply propext
    constructor
    · intro hf k hk
      rw [← hprev k hk]
      exact hf k hk
    · intro hf k hk
      rw [hprev k hk]
      exact hf k hk
  have havail (B : Finset (Fin d)) :
      availableMass q x j B = availableMass q x' j B := by
    unfold availableMass
    apply Finset.sum_congr rfl
    intro v hv
    simp [hfree v]
  by_cases hj : j ∈ S
  · have hforce :
        (PrefixValid x j.val ∧ trackingError q x j.val ≤ 1 / 20 ∧
          Free x j.val (y j)) =
        (PrefixValid x' j.val ∧ trackingError q x' j.val ≤ 1 / 20 ∧
          Free x' j.val (y j)) := by
      simp [hvalid, htrack, hfree]
    have hforce' :
        (PrefixValid x j.val ∧ trackingError q x j.val ≤ (20 : ℝ)⁻¹ ∧
          Free x j.val (y j)) =
        (PrefixValid x' j.val ∧ trackingError q x' j.val ≤ (20 : ℝ)⁻¹ ∧
          Free x' j.val (y j)) := by
      simpa [one_div] using hforce
    simp [forcingStepWeight, hj, hforce']
  · have hOrd : ordinaryWeight q x j (pendingLabels S y j) z =
      ordinaryWeight q x' j (pendingLabels S y j) z := by
        simp [ordinaryWeight, hvalid, htrack, havail, hfree]
    simp [forcingStepWeight, hj, hOrd]

private theorem ordinaryWeight_nonneg {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (hn : ∀ i y, 0 ≤ q i y)
    (x : Injection.Path t d) (j : Fin t) (B : Finset (Fin d)) (z : Option (Fin d)) :
    0 ≤ ordinaryWeight q x j B z := by
  classical
  by_cases hv : PrefixValid x j.val
  · by_cases he : trackingError q x j.val ≤ 1 / 20
    · have he' : trackingError q x j.val ≤ (20 : ℝ)⁻¹ := by simpa using he
      by_cases hm : 0 < availableMass q x j B
      · cases z with
        | none => simp [ordinaryWeight, hv, he', hm]
        | some y =>
            by_cases ha : Free x j.val y ∧ y ∉ B
            · simp [ordinaryWeight, hv, he', hm, ha]
              exact div_nonneg (hn j y) hm.le
            · simp [ordinaryWeight, hv, he', hm, ha]
      · cases z <;> simp [ordinaryWeight, hv, he', hm]
    · have he' : ¬ trackingError q x j.val ≤ (20 : ℝ)⁻¹ := by simpa using he
      cases z <;> simp [ordinaryWeight, hv, he']
  · cases z <;> simp [ordinaryWeight, hv]

private theorem forcingStepWeight_nonneg {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (hn : ∀ i y, 0 ≤ q i y)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Injection.Path t d)
    (j : Fin t) (z : Option (Fin d)) :
  0 ≤ forcingStepWeight q S y x j z := by
  classical
  by_cases hj : j ∈ S
  · by_cases hv : PrefixValid x j.val
    · by_cases he : trackingError q x j.val ≤ 1 / 20
      · have he' : trackingError q x j.val ≤ (20 : ℝ)⁻¹ := by simpa using he
        by_cases hf : Free x j.val (y j)
        · cases z with
          | none => simp [forcingStepWeight, hj, hv, he', hf]
          | some z =>
              by_cases hz : z = y j <;> simp [forcingStepWeight, hj, hv, he', hf, hz]
        · cases z with
          | none => simp [forcingStepWeight, hj, hv, he', hf]
          | some z => simp [forcingStepWeight, hj, hv, he', hf]
      · cases z with
        | none =>
            have he' : ¬ trackingError q x j.val ≤ (20 : ℝ)⁻¹ := by simpa using he
            simp [forcingStepWeight, hj, hv, he']
        | some z =>
            have he' : ¬ trackingError q x j.val ≤ (20 : ℝ)⁻¹ := by simpa using he
            simp [forcingStepWeight, hj, hv, he']
    · cases z with
      | none => simp [forcingStepWeight, hj, hv]
      | some z => simp [forcingStepWeight, hj, hv]
  · simpa [forcingStepWeight, hj] using
      ordinaryWeight_nonneg q hn x j (pendingLabels S y j) z

private theorem ordinaryWeight_sum_one {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (x : Injection.Path t d) (j : Fin t) (B : Finset (Fin d)) :
    ∑ z : Option (Fin d), ordinaryWeight q x j B z = 1 := by
  classical
  by_cases hactive : PrefixValid x j.val ∧ trackingError q x j.val ≤ 1 / 20 ∧
      0 < availableMass q x j B
  · have hmass : (∑ y, if Free x j.val y ∧ y ∉ B then q j y else 0) =
        availableMass q x j B := rfl
    have hsum :
        (∑ y, if Free x j.val y ∧ y ∉ B then
          q j y / availableMass q x j B else 0) = 1 := by
      calc
        _ = ∑ y, (if Free x j.val y ∧ y ∉ B then q j y else 0) /
              availableMass q x j B := by
                apply Finset.sum_congr rfl
                intro y hy
                by_cases hallowed : Free x j.val y ∧ y ∉ B <;> simp [hallowed]
        _ = (∑ y, if Free x j.val y ∧ y ∉ B then q j y else 0) /
              availableMass q x j B := by rw [Finset.sum_div]
        _ = 1 := by rw [hmass, div_self hactive.2.2.ne']
    have hactive' : PrefixValid x j.val ∧ trackingError q x j.val ≤
        (20 : ℝ)⁻¹ ∧ 0 < availableMass q x j B := by
      simpa using hactive
    simpa [ordinaryWeight, hactive', Fintype.sum_option, one_div] using hsum
  · have hactive' : ¬(PrefixValid x j.val ∧ trackingError q x j.val ≤
        (20 : ℝ)⁻¹ ∧ 0 < availableMass q x j B) := by
      simpa using hactive
    simp [ordinaryWeight, hactive', Fintype.sum_option, one_div]

private theorem forcingStepWeight_sum_one {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (S : Finset (Fin t)) (y : Fin t → Fin d)
    (x : Injection.Path t d) (j : Fin t) :
    ∑ z : Option (Fin d), forcingStepWeight q S y x j z = 1 := by
  classical
  by_cases hj : j ∈ S
  · by_cases hforce :
        PrefixValid x j.val ∧ trackingError q x j.val ≤ 1 / 20 ∧
          Free x j.val (y j)
    · simpa [forcingStepWeight, hj, hforce, Fintype.sum_option]
    · simpa [forcingStepWeight, hj, hforce, Fintype.sum_option]
  · simpa [forcingStepWeight, hj] using
      ordinaryWeight_sum_one q x j (pendingLabels S y j)

private def failKernel {d : ℕ} : FinProb (Option (Fin d)) where
  w z := if z = none then 1 else 0
  nonneg z := by split_ifs <;> norm_num
  sum_eq_one := by simp [Fintype.sum_option]

noncomputable def forcingKernel {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (hn : ∀ i y, 0 ≤ q i y)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (j : Fin t)
    (h : Fin j.val → Option (Fin d)) : FinProb (Option (Fin d)) where
  w z := forcingStepWeight q S y (pathFromPrefix j h) j z
  nonneg z := forcingStepWeight_nonneg q hn S y (pathFromPrefix j h) j z
  sum_eq_one := forcingStepWeight_sum_one q S y (pathFromPrefix j h) j

noncomputable def forcingKernelFamily {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (hn : ∀ i y, 0 ≤ q i y)
    (S : Finset (Fin t)) (y : Fin t → Fin d) :
    ∀ m, (Fin m → Option (Fin d)) → FinProb (Option (Fin d)) :=
  fun m h => if hm : m < t then forcingKernel q hn S y ⟨m, hm⟩ h else failKernel

noncomputable def triangularLaw {α : Type*} [Fintype α] [DecidableEq α]
    (K : ∀ n, (Fin n → α) → FinProb α) : (n : ℕ) → FinProb (Fin n → α)
  | 0 =>
      { w := fun _ => 1
        nonneg := by intro; norm_num
        sum_eq_one := by simp }
  | n + 1 =>
      FinProb.map (FinProb.bind (triangularLaw K n) (fun h => K n h))
        (fun hp => appendLast hp.1 hp.2)

theorem triangularLaw_weight {α : Type*} [Fintype α] [DecidableEq α]
    (K : ∀ n, (Fin n → α) → FinProb α) :
    ∀ n (x : Fin n → α),
      (triangularLaw K n).w x =
        ∏ j : Fin n, (K j.val (takePrefix (Nat.le_of_lt j.isLt) x)).w (x j) := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [triangularLaw]
  | succ n ih =>
      intro x
      let h := takePrefix (Nat.le_succ n) x
      let z := lastValue x
      have hmap :
          (FinProb.map (FinProb.bind (triangularLaw K n) (fun g => K n g))
            (fun p => appendLast p.1 p.2)).w x =
            (FinProb.bind (triangularLaw K n) (fun g => K n g)).w (h, z) := by
        unfold FinProb.map
        change
          (∑ p : (Fin n → α) × α,
            if appendLast p.1 p.2 = x then
              (FinProb.bind (triangularLaw K n) (fun g => K n g)).w p else 0) = _
        rw [Finset.sum_eq_single (h, z)]
        · simp [h, z, appendLast_takePrefix_lastValue, FinProb.bind]
        · intro p hp hpne
          have hnot : appendLast p.1 p.2 ≠ x := by
            intro heq
            apply hpne
            apply Prod.ext
            · have hh := congrArg (takePrefix (Nat.le_succ n)) heq
              simpa [h, takePrefix_appendLast] using hh
            · have hh := congrArg lastValue heq
              simpa [z, lastValue_appendLast] using hh
          simp [hnot, FinProb.bind]
        · simp
      have hprefixCast (j : Fin n) :
          takePrefix (Nat.le_of_lt (Fin.castSucc j).isLt) x =
            takePrefix (Nat.le_of_lt j.isLt) h := by
        funext k
        simp [h, takePrefix]
      calc
        (triangularLaw K (n + 1)).w x =
            (triangularLaw K n).w h * (K n h).w z := by
              change
                (FinProb.map (FinProb.bind (triangularLaw K n) (fun g => K n g))
                  (fun p => appendLast p.1 p.2)).w x = _
              rw [hmap]
              rfl
        _ = (∏ j : Fin n,
              (K j.val (takePrefix (Nat.le_of_lt j.isLt) h)).w (h j)) *
              (K n h).w z := by rw [ih h]
        _ = ∏ j : Fin (n + 1),
              (K j.val (takePrefix (Nat.le_of_lt j.isLt) x)).w (x j) := by
              rw [Fin.prod_univ_castSucc]
              apply congrArg₂ (fun u v => u * v)
              · apply Finset.prod_congr rfl
                intro j hj
                simp [hprefixCast, h, takePrefix, Fin.castSucc]
                have hidx :
                    (⟨j.val, by omega⟩ : Fin (n + 1)) = Fin.castAdd 1 j := by
                  apply Fin.ext
                  rfl
                rw [hidx]
              · simp [h, z, takePrefix, lastValue, Fin.last, Fin.val_last]

theorem forcingWeight_eq_triangularLaw_weight {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (hn : ∀ i y, 0 ≤ q i y)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Injection.Path t d) :
    forcingWeight q S y x =
      (triangularLaw (forcingKernelFamily q hn S y) t).w x := by
  classical
  rw [triangularLaw_weight]
  unfold forcingWeight
  apply Finset.prod_congr rfl
  intro j hj
  have hjt : j.val < t := j.isLt
  have hprev :
      ∀ k : Fin t, k.val < j.val →
        x k = pathFromPrefix j (takePrefix (Nat.le_of_lt j.isLt) x) k := by
    intro k hk
    simp [pathFromPrefix, takePrefix, hk]
  have hstep := forcingStepWeight_prefix_congr q S y x
    (pathFromPrefix j (takePrefix (Nat.le_of_lt j.isLt) x)) j (x j) hprev
  simpa [forcingKernelFamily, forcingKernel, hjt] using hstep

theorem forcingKernel_expect_step {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (hn : ∀ i y, 0 ≤ q i y)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Injection.Path t d)
    (j a : Fin t) :
    (forcingKernel q hn S y j (takePrefix (Nat.le_of_lt j.isLt) x)).expect
        (fun z => z.elim 0 (q a)) =
      forcedStepDrift q S y x a j := by
  classical
  change
    (∑ z, forcingStepWeight q S y
      (pathFromPrefix j (takePrefix (Nat.le_of_lt j.isLt) x)) j z *
        z.elim 0 (q a)) =
      ∑ z, forcingStepWeight q S y x j z * z.elim 0 (q a)
  apply Finset.sum_congr rfl
  intro z hz
  have hprev : ∀ k : Fin t, k.val < j.val →
      x k = pathFromPrefix j (takePrefix (Nat.le_of_lt j.isLt) x) k := by
    intro k hk
    simp [pathFromPrefix, takePrefix, hk]
  rw [(forcingStepWeight_prefix_congr q S y x
    (pathFromPrefix j (takePrefix (Nat.le_of_lt j.isLt) x)) j z hprev).symm]

theorem triangularLaw_expect_final {α : Type*} [Fintype α] [DecidableEq α]
    (K : ∀ n, (Fin n → α) → FinProb α) (n : ℕ)
    (F : (Fin n → α) → α → ℝ) :
    (triangularLaw K (n + 1)).expect
        (fun x => F (takePrefix (Nat.le_succ n) x) (lastValue x)) =
      ∑ h, (triangularLaw K n).w h * (K n h).expect (F h) := by
  change
    (FinProb.map (FinProb.bind (triangularLaw K n) (fun h => K n h))
      (fun hp => appendLast hp.1 hp.2)).expect
        (fun x => F (takePrefix (Nat.le_succ n) x) (lastValue x)) = _
  rw [FinProb.map_expect]
  simpa [takePrefix_appendLast, lastValue_appendLast] using
    (FinProb.bind_expect (triangularLaw K n) (fun h => K n h) F)

theorem triangularLaw_expect_init {α : Type*} [Fintype α] [DecidableEq α]
    (K : ∀ n, (Fin n → α) → FinProb α) (n : ℕ)
    (F : (Fin n → α) → ℝ) :
    (triangularLaw K (n + 1)).expect
        (fun x => F (takePrefix (Nat.le_succ n) x)) =
      (triangularLaw K n).expect F := by
  have h := triangularLaw_expect_final K n (fun h _ => F h)
  calc
    (triangularLaw K (n + 1)).expect
        (fun x => F (takePrefix (Nat.le_succ n) x)) =
        (triangularLaw K (n + 1)).expect
          (fun x => (fun h _ => F h)
            (takePrefix (Nat.le_succ n) x) (lastValue x)) := by rfl
    _ = ∑ h, (triangularLaw K n).w h * (K n h).expect (fun _ => F h) := h
    _ = (triangularLaw K n).expect F := by
          change
            (∑ h, (triangularLaw K n).w h * (K n h).expect (fun _ => F h)) =
              ∑ h, (triangularLaw K n).w h * F h
          apply Finset.sum_congr rfl
          intro h hh
          rw [FinProb.expect_const]

theorem triangularLaw_prefix_expect {α : Type*} [Fintype α] [DecidableEq α]
    (K : ∀ n, (Fin n → α) → FinProb α) :
    ∀ {m n : ℕ} (hm : m ≤ n) (F : (Fin m → α) → ℝ),
      (triangularLaw K n).expect (fun x => F (takePrefix hm x)) =
        (triangularLaw K m).expect F := by
  intro m n
  induction n with
  | zero =>
      intro hm F
      have hm0 : m = 0 := by omega
      subst m
      have hid (x : Fin 0 → α) : takePrefix hm x = x := by
        funext k
        exact Fin.elim0 k
      have hfun :
          (fun x : Fin 0 → α => F (takePrefix hm x)) = fun x => F x := by
        funext x
        exact congrArg F (hid x)
      exact congrArg (fun G => (triangularLaw K 0).expect G) hfun
  | succ n ih =>
      intro hm F
      by_cases hmn : m ≤ n
      · have hcomp (x : Fin (n + 1) → α) :
              takePrefix hm x =
                takePrefix hmn (takePrefix (Nat.le_succ n) x) := by
          funext k
          simp [takePrefix]
        have hfun :
            (fun x => F (takePrefix hm x)) =
              (fun x => F (takePrefix hmn (takePrefix (Nat.le_succ n) x))) := by
          funext x
          exact congrArg F (hcomp x)
        rw [hfun]
        exact (triangularLaw_expect_init K n (fun x => F (takePrefix hmn x))).trans
          (ih hmn F)
      · have hEq : m = n + 1 := by omega
        subst m
        have hmEq : n + 1 ≤ n + 1 := Nat.le_refl _
        have hprefixId (x : Fin (n + 1) → α) : takePrefix hmEq x = x := by
          funext k
          simp [takePrefix]
        have hproof : hm = hmEq := Subsingleton.elim _ _
        have hfun : (fun x => F (takePrefix hm x)) = fun x => F x := by
          funext x
          rw [hproof, hprefixId]
        exact congrArg (fun G => (triangularLaw K (n + 1)).expect G) hfun

theorem triangularLaw_last_centered_fiber {α : Type*} [Fintype α] [DecidableEq α]
    (K : ∀ n, (Fin n → α) → FinProb α) (n : ℕ)
    (h : Fin n → α) (X : α → ℝ) :
    (∑ x : Fin (n + 1) → α,
      if takePrefix (Nat.le_succ n) x = h then
        (triangularLaw K (n + 1)).w x *
          (X (lastValue x) - (K n h).expect X) else 0) = 0 := by
  let F : (Fin n → α) → α → ℝ := fun g z =>
    if g = h then X z - (K n h).expect X else 0
  have hsum :
      (∑ x : Fin (n + 1) → α,
        if takePrefix (Nat.le_succ n) x = h then
          (triangularLaw K (n + 1)).w x *
            (X (lastValue x) - (K n h).expect X) else 0) =
        (triangularLaw K (n + 1)).expect
          (fun x => F (takePrefix (Nat.le_succ n) x) (lastValue x)) := by
    change
      (∑ x : Fin (n + 1) → α,
        if takePrefix (Nat.le_succ n) x = h then
          (triangularLaw K (n + 1)).w x *
            (X (lastValue x) - (K n h).expect X) else 0) =
      ∑ x, (triangularLaw K (n + 1)).w x *
        (if takePrefix (Nat.le_succ n) x = h then
          X (lastValue x) - (K n h).expect X else 0)
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hx' : takePrefix (Nat.le_succ n) x = h <;> simp [hx']
  rw [hsum, triangularLaw_expect_final]
  dsimp [F]
  calc
    (∑ g, (triangularLaw K n).w g *
        (K n g).expect (fun z => if g = h then X z - (K n h).expect X else 0)) =
      ∑ g, if g = h then
        (triangularLaw K n).w g *
          (K n g).expect (fun z => X z - (K n h).expect X) else 0 := by
          apply Finset.sum_congr rfl
          intro g hg
          by_cases hgh : g = h
          · simp [hgh]
          · simp [hgh, FinProb.expect]
    _ = 0 := by
      have hcenter :
          (K n h).expect (fun z => X z - (K n h).expect X) = 0 := by
        calc
          (K n h).expect (fun z => X z - (K n h).expect X) =
              (K n h).expect (fun z => X z + (-(K n h).expect X)) := by
                congr 1
          _ = (K n h).expect X + (K n h).expect (fun _ => -(K n h).expect X) :=
            FinProb.expect_add _ _ _
          _ = (K n h).expect X + -(K n h).expect X := by
            rw [FinProb.expect_const]
          _ = 0 := by ring
      rw [Finset.sum_eq_single h]
      · simp [hcenter]
      · intro g hg hne
        simp [hne]
      · simp

theorem forcingLaw_centered_step {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (hn : ∀ i y, 0 ≤ q i y)
    (hs : ∀ i, ∑ y, q i y = 1) (S : Finset (Fin t))
    (y : Fin t → Fin d) (j a : Fin t) (h : Fin j.val → Option (Fin d)) :
    (∑ x : Injection.Path t d,
      if takePrefix (Nat.le_of_lt j.isLt) x = h then
        forcingWeight q S y x *
          ((x j).elim 0 (q a) - forcedStepDrift q S y x a j) else 0) = 0 := by
  classical
  let K := forcingKernelFamily q hn S y
  let P := forcingLaw q hn hs S y
  let X : Option (Fin d) → ℝ := fun z => z.elim 0 (q a)
  let m := j.val + 1
  have hm : m ≤ t := Nat.succ_le_of_lt j.isLt
  let F : (Fin m → Option (Fin d)) → ℝ := fun p =>
    if takePrefix (Nat.le_succ j.val) p = h then
      X (lastValue p) - (K j.val h).expect X else 0
  have hpref (x : Injection.Path t d) :
      takePrefix (Nat.le_succ j.val) (takePrefix hm x) =
        takePrefix (Nat.le_of_lt j.isLt) x := by
    funext k
    simp [takePrefix]
  have hlast (x : Injection.Path t d) :
      lastValue (takePrefix hm x) = x j := by
    simp [lastValue, takePrefix]
  have hkernelDrift (x : Injection.Path t d) :
      (K j.val (takePrefix (Nat.le_of_lt j.isLt) x)).expect X =
        forcedStepDrift q S y x a j := by
    simpa [K, forcingKernelFamily, j.isLt] using
      forcingKernel_expect_step q hn S y x j a
  have hpoint (x : Injection.Path t d) :
      (if takePrefix (Nat.le_of_lt j.isLt) x = h then
        X (x j) - forcedStepDrift q S y x a j else 0) =
        F (takePrefix hm x) := by
    dsimp [F]
    by_cases heq : takePrefix (Nat.le_of_lt j.isLt) x = h
    · rw [hpref x]
      simp only [if_pos heq]
      rw [hlast x]
      rw [← hkernelDrift x, heq]
    · simp [F, heq, hpref x]
  have hweight (x : Injection.Path t d) :
      P.w x = (triangularLaw K t).w x := by
    dsimp [P, K, forcingLaw]
    exact forcingWeight_eq_triangularLaw_weight q hn S y x
  have hexpect (G : Injection.Path t d → ℝ) :
      P.expect G = (triangularLaw K t).expect G := by
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro x hx
    rw [hweight x]
  have hsumExpect :
      (∑ x : Injection.Path t d,
        if takePrefix (Nat.le_of_lt j.isLt) x = h then
          P.w x * (X (x j) - forcedStepDrift q S y x a j) else 0) =
        P.expect (fun x =>
          if takePrefix (Nat.le_of_lt j.isLt) x = h then
            X (x j) - forcedStepDrift q S y x a j else 0) := by
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro x hx
    by_cases heq : takePrefix (Nat.le_of_lt j.isLt) x = h <;> simp [heq]
  have hsumExpect' :
      (∑ x : Injection.Path t d,
        if takePrefix (Nat.le_of_lt j.isLt) x = h then
          forcingWeight q S y x *
            (X (x j) - forcedStepDrift q S y x a j) else 0) =
        P.expect (fun x =>
          if takePrefix (Nat.le_of_lt j.isLt) x = h then
            X (x j) - forcedStepDrift q S y x a j else 0) := by
    simpa [P, forcingLaw] using hsumExpect
  have hcentExp :
      P.expect (fun x =>
        if takePrefix (Nat.le_of_lt j.isLt) x = h then
          X (x j) - forcedStepDrift q S y x a j else 0) = 0 := by
    calc
      _ = P.expect (fun x => F (takePrefix hm x)) := by
        apply congrArg (fun G => P.expect G)
        funext x
        exact hpoint x
      _ = (triangularLaw K t).expect (fun x => F (takePrefix hm x)) :=
        hexpect _
      _ = (triangularLaw K m).expect F :=
        triangularLaw_prefix_expect K hm F
      _ = 0 := by
        have hfiber := triangularLaw_last_centered_fiber K j.val h X
        have hfiberExp :
            (triangularLaw K m).expect F =
              ∑ p : Fin m → Option (Fin d),
                if takePrefix (Nat.le_succ j.val) p = h then
                  (triangularLaw K m).w p *
                    (X (lastValue p) - (K j.val h).expect X) else 0 := by
          change (∑ p, (triangularLaw K m).w p * F p) = _
          apply Finset.sum_congr rfl
          intro p hp
          by_cases hph : takePrefix (Nat.le_succ j.val) p = h <;> simp [F, hph]
        rw [hfiberExp]
        simpa [m] using hfiber
  exact hsumExpect'.trans hcentExp


end HypercubeRamsey.Lane_q_inj_comp
