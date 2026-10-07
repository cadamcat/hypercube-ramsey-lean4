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
    sorry

end HypercubeRamsey
