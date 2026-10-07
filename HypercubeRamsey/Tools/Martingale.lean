import HypercubeRamsey.Framework.FinProb

/-!
# Finite likelihood-ratio martingales

For two laws on a finite path space, the ratio of prefix probabilities is a martingale under the reference
law when the target law is absolutely continuous with respect to it. Bounded prefix stopping times preserve
its expectation.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- The length-`m` prefix of a path of length `n`. -/
def pathPrefix {α : Type*} {n m : ℕ} (hm : m ≤ n) (ω : Fin n → α) : Fin m → α :=
  fun i => ω ⟨i.val, lt_of_lt_of_le i.isLt hm⟩

/-- Probability of a specified prefix under a finite path law. -/
noncomputable def prefixProbability {α : Type*} [Fintype α] {n : ℕ}
    (P : FinProb (Fin n → α)) (m : ℕ) (hm : m ≤ n) (h : Fin m → α) : ℝ :=
  P.pr (fun ω => pathPrefix hm ω = h)

/-- Prefix likelihood ratio `dP/dQ`, set to zero on a `Q`-null prefix. -/
noncomputable def prefixLikelihoodRatio {α : Type*} [Fintype α] {n : ℕ}
    (P Q : FinProb (Fin n → α)) (m : ℕ) (hm : m ≤ n) (h : Fin m → α) : ℝ :=
  if prefixProbability Q m hm h = 0 then 0 else
    prefixProbability P m hm h / prefixProbability Q m hm h

/-- A stopping time for the prefix filtration: whether it has stopped by `m` depends only on the first `m`
coordinates. -/
def IsPrefixStoppingTime {α : Type*} {n : ℕ} (τ : (Fin n → α) → Fin (n + 1)) : Prop :=
  ∀ (m : ℕ) (hm : m ≤ n) (ω ω' : Fin n → α),
    (∀ i : Fin m, pathPrefix hm ω i = pathPrefix hm ω' i) →
      ((τ ω).val ≤ m ↔ (τ ω').val ≤ m)

set_option maxHeartbeats 1000000 in
/-- X-Martingale: likelihood ratios of finite adaptive prefixes form a martingale under `Q`; bounded
prefix stopping preserves expectation one. -/
theorem xLikelihoodRatioMartingale {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (P Q : FinProb (Fin n → α))
    (habsolutelyContinuous : ∀ ω, P.w ω > 0 → Q.w ω > 0)
    (m : ℕ) (hm : m < n) (h : Fin m → α) :
    (∑ a : α,
      prefixProbability Q (m + 1) (Nat.succ_le_of_lt hm) (Fin.snoc h a) *
        prefixLikelihoodRatio P Q (m + 1) (Nat.succ_le_of_lt hm) (Fin.snoc h a)) =
      prefixProbability Q m (Nat.le_of_lt hm) h *
        prefixLikelihoodRatio P Q m (Nat.le_of_lt hm) h ∧
    (∀ τ : (Fin n → α) → Fin (n + 1), IsPrefixStoppingTime τ →
      Q.expect (fun ω =>
        prefixLikelihoodRatio P Q (τ ω).val (Nat.le_of_lt_succ (τ ω).isLt)
          (pathPrefix (Nat.le_of_lt_succ (τ ω).isLt) ω)) = 1) := by
  classical
  have hsplit (R : FinProb (Fin n → α)) :
      (∑ a : α,
        prefixProbability R (m + 1) (Nat.succ_le_of_lt hm) (Fin.snoc h a)) =
        prefixProbability R m (Nat.le_of_lt hm) h := by
    unfold prefixProbability FinProb.pr
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω hω
    have hchar (a : α) :
        pathPrefix (Nat.succ_le_of_lt hm) ω = Fin.snoc h a ↔
          pathPrefix (Nat.le_of_lt hm) ω = h ∧ ω ⟨m, hm⟩ = a := by
      constructor
      · intro heq
        refine ⟨?_, ?_⟩
        · funext i
          have hi := congrFun heq i.castSucc
          simpa [pathPrefix] using hi
        · have hi := congrFun heq (Fin.last m)
          simpa [pathPrefix] using hi
      · rintro ⟨hh, ha⟩
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa [pathPrefix] using ha
        · simpa [pathPrefix] using congrFun hh i
    by_cases hh : pathPrefix (Nat.le_of_lt hm) ω = h
    · simp [hchar, hh]
    · have hmiss (a : α) :
          pathPrefix (Nat.succ_le_of_lt hm) ω ≠ Fin.snoc h a := by
        intro heq
        exact hh (hchar a |>.mp heq).1
      simp [hchar, hh, hmiss]
  have hprefixAC {r : ℕ} (hr : r ≤ n) (g : Fin r → α)
      (hq : prefixProbability Q r hr g = 0) :
      prefixProbability P r hr g = 0 := by
    have hpoint : ∀ ω, pathPrefix hr ω = g → P.w ω = 0 := by
      intro ω hmatch
      by_contra hp
      have hp' : 0 < P.w ω := lt_of_le_of_ne (P.nonneg ω) (Ne.symm hp)
      have hq' := habsolutelyContinuous ω hp'
      letI : DecidablePred (fun ω' => pathPrefix hr ω' = g) :=
        fun ω' => Classical.propDecidable _
      have hle' :
          (if pathPrefix hr ω = g then Q.w ω else 0) ≤
            ∑ ω', if pathPrefix hr ω' = g then Q.w ω' else 0 :=
        Finset.single_le_sum
          (f := fun ω' => if pathPrefix hr ω' = g then Q.w ω' else 0)
          (fun ω' hω' => by
            split_ifs with hω''
            · exact Q.nonneg ω'
            · exact le_rfl)
          (Finset.mem_univ ω)
      have hle : Q.w ω ≤ Q.pr (fun ω => pathPrefix hr ω = g) := by
        simpa [FinProb.pr, hmatch] using hle'
      have hqzero : Q.pr (fun ω => pathPrefix hr ω = g) = 0 := by
        simpa [prefixProbability] using hq
      linarith
    unfold prefixProbability FinProb.pr
    apply Finset.sum_eq_zero
    intro ω hω
    by_cases hm' : pathPrefix hr ω = g
    · simp [hm', hpoint ω hm']
    · simp [hm']
  have hterm {r : ℕ} (hr : r ≤ n) (g : Fin r → α) :
      prefixProbability Q r hr g * prefixLikelihoodRatio P Q r hr g =
        prefixProbability P r hr g := by
    by_cases hq : prefixProbability Q r hr g = 0
    · simp [prefixLikelihoodRatio, hq, hprefixAC hr g hq]
    · rw [prefixLikelihoodRatio, if_neg hq]
      field_simp
  have hprefixMass {r : ℕ} (hr : r ≤ n) (R : FinProb (Fin n → α))
      (g : Fin r → α) :
      prefixProbability R r hr g =
        ∑ ω, if pathPrefix hr ω = g then R.w ω else 0 := by
    classical
    unfold prefixProbability FinProb.pr
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases heq : pathPrefix hr ω = g <;> simp [heq]
  have hprefixSum {r : ℕ} (hr : r ≤ n) (C : (Fin r → α) → Prop)
      (R : FinProb (Fin n → α)) :
      R.pr (fun ω => C (pathPrefix hr ω)) =
        ∑ g, if C g then prefixProbability R r hr g else 0 := by
    classical
    unfold FinProb.pr
    calc
      (∑ ω, if C (pathPrefix hr ω) then R.w ω else 0) =
          ∑ ω, ∑ g, if pathPrefix hr ω = g ∧ C g then R.w ω else 0 := by
        apply Finset.sum_congr rfl
        intro ω hω
        symm
        rw [Finset.sum_eq_single (pathPrefix hr ω)]
        · simp
        · intro g hg hne
          have hne' : pathPrefix hr ω ≠ g := fun heq => hne heq.symm
          simp [hne']
        · simp
      _ = ∑ g, ∑ ω, if pathPrefix hr ω = g ∧ C g then R.w ω else 0 := Finset.sum_comm
      _ = ∑ g, if C g then ∑ ω, if pathPrefix hr ω = g then R.w ω else 0 else 0 := by
        apply Finset.sum_congr rfl
        intro g hg
        by_cases hC : C g <;> simp [hC]
      _ = ∑ g, if C g then R.pr (fun ω => pathPrefix hr ω = g) else 0 := by
        apply Finset.sum_congr rfl
        intro g hg
        by_cases hC : C g
        · simp [hC]
          exact (hprefixMass hr R g).symm
        · simp [hC]
  have hprefixLR {r : ℕ} (hr : r ≤ n) (C : (Fin r → α) → Prop) :
      Q.expect (fun ω => if C (pathPrefix hr ω) then
        prefixLikelihoodRatio P Q r hr (pathPrefix hr ω) else 0) =
        P.pr (fun ω => C (pathPrefix hr ω)) := by
    classical
    unfold FinProb.expect
    calc
      (∑ ω, Q.w ω * if C (pathPrefix hr ω) then
          prefixLikelihoodRatio P Q r hr (pathPrefix hr ω) else 0) =
          ∑ ω, ∑ g, if pathPrefix hr ω = g ∧ C g then
            Q.w ω * prefixLikelihoodRatio P Q r hr g else 0 := by
        apply Finset.sum_congr rfl
        intro ω hω
        symm
        rw [Finset.sum_eq_single (pathPrefix hr ω)]
        · simp
        · intro g hg hne
          have hne' : pathPrefix hr ω ≠ g := fun heq => hne heq.symm
          simp [hne']
        · simp
      _ = ∑ g, ∑ ω, if pathPrefix hr ω = g ∧ C g then
            Q.w ω * prefixLikelihoodRatio P Q r hr g else 0 := Finset.sum_comm
      _ = ∑ g, if C g then
            prefixProbability Q r hr g * prefixLikelihoodRatio P Q r hr g else 0 := by
        apply Finset.sum_congr rfl
        intro g hg
        by_cases hC : C g
        · simp only [hC, and_true, ite_true]
          calc
            (∑ ω, if pathPrefix hr ω = g then
                Q.w ω * prefixLikelihoodRatio P Q r hr g else 0) =
                (∑ ω, if pathPrefix hr ω = g then Q.w ω else 0) *
                  prefixLikelihoodRatio P Q r hr g := by
              calc
                (∑ ω, if pathPrefix hr ω = g then
                    Q.w ω * prefixLikelihoodRatio P Q r hr g else 0) =
                    ∑ ω, (if pathPrefix hr ω = g then Q.w ω else 0) *
                      prefixLikelihoodRatio P Q r hr g := by
                  apply Finset.sum_congr rfl
                  intro ω hω
                  by_cases heq : pathPrefix hr ω = g <;> simp [heq]
                _ = (∑ ω, if pathPrefix hr ω = g then Q.w ω else 0) *
                    prefixLikelihoodRatio P Q r hr g := (Finset.sum_mul ..).symm
            _ = prefixProbability Q r hr g * prefixLikelihoodRatio P Q r hr g :=
              congrArg (fun z => z * prefixLikelihoodRatio P Q r hr g)
                (hprefixMass hr Q g).symm
        · simp [hC]
      _ = ∑ g, if C g then prefixProbability P r hr g else 0 := by
        apply Finset.sum_congr rfl
        intro g hg
        by_cases hC : C g
        · simp [hC, hterm hr g]
        · simp [hC]
      _ = P.pr (fun ω => C (pathPrefix hr ω)) := (hprefixSum hr C P).symm
  have hprefixMono {m r : ℕ} (hmr : m ≤ r) (hr : r ≤ n) (ω ω' : Fin n → α)
      (heq : pathPrefix hr ω = pathPrefix hr ω') :
      pathPrefix (hmr.trans hr) ω = pathPrefix (hmr.trans hr) ω' := by
    funext i
    have hi := congrFun heq (Fin.castLE hmr i)
    simpa [pathPrefix] using hi
  refine ⟨?_, ?_⟩
  · calc
      (∑ a : α,
        prefixProbability Q (m + 1) (Nat.succ_le_of_lt hm) (Fin.snoc h a) *
          prefixLikelihoodRatio P Q (m + 1) (Nat.succ_le_of_lt hm) (Fin.snoc h a)) =
          ∑ a : α, prefixProbability P (m + 1) (Nat.succ_le_of_lt hm) (Fin.snoc h a) := by
            apply Finset.sum_congr rfl
            intro a ha
            exact hterm (Nat.succ_le_of_lt hm) (Fin.snoc h a)
      _ = prefixProbability P m (Nat.le_of_lt hm) h := hsplit P
      _ = prefixProbability Q m (Nat.le_of_lt hm) h *
            prefixLikelihoodRatio P Q m (Nat.le_of_lt hm) h :=
          (hterm (Nat.le_of_lt hm) h).symm
  · intro τ hτ
    have hstopEq {r : ℕ} (hr : r ≤ n) (ω ω' : Fin n → α)
        (heq : pathPrefix hr ω = pathPrefix hr ω')
        (hω : (τ ω).val ≤ r) (hω' : (τ ω').val ≤ r) : τ ω = τ ω' := by
      apply Fin.ext
      have hleft := hτ (τ ω).val (hω.trans hr) ω ω'
        (fun i => congrFun (hprefixMono hω hr ω ω' heq) i)
      have hright := hτ (τ ω').val (hω'.trans hr) ω ω'
        (fun i => congrFun (hprefixMono hω' hr ω ω' heq) i)
      exact Nat.le_antisymm (hright.mpr le_rfl) (hleft.mp le_rfl)
    have hstopInvariant (r : Fin (n + 1)) (hr : r.val ≤ n) (ω ω' : Fin n → α)
        (heq : pathPrefix hr ω = pathPrefix hr ω') :
        (τ ω = r) ↔ (τ ω' = r) := by
      have hlevel := hτ r.val hr ω ω' (fun i => congrFun heq i)
      constructor
      · intro h
        have hω : (τ ω).val ≤ r.val := by simp [h]
        have hω' : (τ ω').val ≤ r.val := hlevel.mp hω
        have heqτ := hstopEq hr ω ω' heq hω hω'
        exact heqτ.symm.trans h
      · intro h
        have hω' : (τ ω').val ≤ r.val := by simp [h]
        have hω : (τ ω).val ≤ r.val := hlevel.mpr hω'
        have heqτ := hstopEq hr ω ω' heq hω hω'
        exact heqτ.trans h
    have hdecomp (ω : Fin n → α) :
        prefixLikelihoodRatio P Q (τ ω).val (Nat.le_of_lt_succ (τ ω).isLt)
          (pathPrefix (Nat.le_of_lt_succ (τ ω).isLt) ω) =
        ∑ r : Fin (n + 1), if τ ω = r then
          prefixLikelihoodRatio P Q r.val (Nat.le_of_lt_succ r.isLt)
            (pathPrefix (Nat.le_of_lt_succ r.isLt) ω) else 0 := by
      classical
      rw [Finset.sum_eq_single (τ ω)]
      · simp
      · intro r hr hne
        have hne' : τ ω ≠ r := fun h => hne h.symm
        simp [hne']
      · simp
    have hstopTerm (r : Fin (n + 1)) :
        Q.expect (fun ω => if τ ω = r then
          prefixLikelihoodRatio P Q r.val (Nat.le_of_lt_succ r.isLt)
            (pathPrefix (Nat.le_of_lt_succ r.isLt) ω) else 0) =
          P.pr (fun ω => τ ω = r) := by
      classical
      let C : (Fin r.val → α) → Prop := fun g =>
        ∃ ω, pathPrefix (Nat.le_of_lt_succ r.isLt) ω = g ∧ τ ω = r
      letI : DecidablePred C := fun g => Classical.propDecidable _
      have hC (ω : Fin n → α) :
          (τ ω = r) ↔ C (pathPrefix (Nat.le_of_lt_succ r.isLt) ω) := by
        constructor
        · intro h
          exact ⟨ω, rfl, h⟩
        · rintro ⟨ω', heq, hτ'⟩
          have hτeq := hstopInvariant r (Nat.le_of_lt_succ r.isLt) ω ω' heq.symm
          exact hτeq.mpr hτ'
      have hfun : (fun ω => if τ ω = r then
          prefixLikelihoodRatio P Q r.val (Nat.le_of_lt_succ r.isLt)
            (pathPrefix (Nat.le_of_lt_succ r.isLt) ω) else 0) =
        (fun ω => if C (pathPrefix (Nat.le_of_lt_succ r.isLt) ω) then
          prefixLikelihoodRatio P Q r.val (Nat.le_of_lt_succ r.isLt)
            (pathPrefix (Nat.le_of_lt_succ r.isLt) ω) else 0) := by
        funext ω
        simp [hC ω]
      rw [hfun]
      have hprob : (fun ω => C (pathPrefix (Nat.le_of_lt_succ r.isLt) ω)) =
          (fun ω => τ ω = r) := by
        funext ω
        exact propext (hC ω).symm
      calc
        Q.expect (fun ω => if C (pathPrefix (Nat.le_of_lt_succ r.isLt) ω) then
            prefixLikelihoodRatio P Q r.val (Nat.le_of_lt_succ r.isLt)
              (pathPrefix (Nat.le_of_lt_succ r.isLt) ω) else 0) =
            P.pr (fun ω => C (pathPrefix (Nat.le_of_lt_succ r.isLt) ω)) :=
          hprefixLR (Nat.le_of_lt_succ r.isLt) C
        _ = P.pr (fun ω => τ ω = r) := congrArg P.pr hprob
    have hdecompExpect :
        Q.expect (fun ω => prefixLikelihoodRatio P Q (τ ω).val
          (Nat.le_of_lt_succ (τ ω).isLt)
          (pathPrefix (Nat.le_of_lt_succ (τ ω).isLt) ω)) =
          ∑ r : Fin (n + 1), Q.expect (fun ω => if τ ω = r then
            prefixLikelihoodRatio P Q r.val (Nat.le_of_lt_succ r.isLt)
              (pathPrefix (Nat.le_of_lt_succ r.isLt) ω) else 0) := by
      calc
        _ = Q.expect (fun ω => ∑ r : Fin (n + 1), if τ ω = r then
              prefixLikelihoodRatio P Q r.val (Nat.le_of_lt_succ r.isLt)
                (pathPrefix (Nat.le_of_lt_succ r.isLt) ω) else 0) := by
          unfold FinProb.expect
          apply Finset.sum_congr rfl
          intro ω hω
          exact congrArg (fun z => Q.w ω * z) (hdecomp ω)
        _ = ∑ r : Fin (n + 1), Q.expect (fun ω => if τ ω = r then
              prefixLikelihoodRatio P Q r.val (Nat.le_of_lt_succ r.isLt)
                (pathPrefix (Nat.le_of_lt_succ r.isLt) ω) else 0) := by
          unfold FinProb.expect
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
    calc
      _ = ∑ r : Fin (n + 1), P.pr (fun ω => τ ω = r) := by
        rw [hdecompExpect]
        apply Finset.sum_congr rfl
        intro r hr
        exact hstopTerm r
      _ = 1 := by
        unfold FinProb.pr
        rw [Finset.sum_comm]
        letI : ∀ r : Fin (n + 1), DecidablePred (fun ω : Fin n → α => τ ω = r) :=
          fun r ω => Classical.propDecidable _
        calc
          (∑ ω, ∑ r : Fin (n + 1), if τ ω = r then P.w ω else 0) =
              ∑ ω, P.w ω := by
            apply Finset.sum_congr rfl
            intro ω hω
            rw [Finset.sum_eq_single (τ ω)]
            · simp
            · intro r hr hne
              have hne' : τ ω ≠ r := fun h => hne h.symm
              simp [hne']
            · simp
          _ = 1 := P.sum_eq_one

end HypercubeRamsey
