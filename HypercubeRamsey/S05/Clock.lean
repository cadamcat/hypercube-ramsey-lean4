import HypercubeRamsey.S05.Centres
import HypercubeRamsey.S05.Clock_q_s05_even

/-!
# L5.1m: actual odd outputs by clock sampling (05:1063–1084)

Given probability rows for the odd roles with column sums at most `θ₀` and small atoms, and per even role a
budget of bounded nonnegative costs on its star with small total mean, the clock lemma (L3.10, scope exponent
`B = 2`) gives an injective assignment satisfying every budget whose joint law is at most `(1 + o(1))` times the
product of the rows on at most `n²` queried rows; each budget fails under the product with probability
`exp(-Ω((t₁ - t₀)² / (n M²)))` by bounded-summand concentration.
-/

namespace HypercubeRamsey

open Classical OAI.HypercubeRamsey Filter

/-- L5.1m (05:1063–1084). -/
theorem L5_1m : ∃ A P : ℝ, ∃ n₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧ (∀ k, 0 ≤ ε k) ∧
    ∀ n ≥ n₀, ∀ (N : ℕ), 2 ^ n ≤ N → N ≤ n * 2 ^ n →
    ∀ {O : Type} [Fintype O] [DecidableEq O] (lab : O → Fin N) (row : OddRole5 n → FinProb O)
      (cost : EvenRole5 n → OddRole5 n → O → ℝ) (M t₀ t₁ : ℝ),
      (∀ x, ∑ b, labMarg (row b) lab x ≤ 1e-8) →
      (∀ b x, labMarg (row b) lab x ≤ (n : ℝ) ^ (-A)) →
      (∀ v b o, 0 ≤ cost v b o ∧ cost v b o ≤ M) →
      (∀ v b o, ¬ (cube n).Adj v.1 b.1 → cost v b o = 0) →
      (∀ v, ∑ b, (row b).expect (cost v b) ≤ t₀) →
      t₀ ≤ t₁ →
      Real.exp (-(2 * (t₁ - t₀) ^ 2 / ((n : ℝ) * M ^ 2))) ≤ (n : ℝ) ^ (-P) →
      ∃ J : FinProb (OddRole5 n → O),
        (∀ ω, J.w ω ≠ 0 → Function.Injective (fun b => lab (ω b)) ∧ ∀ v, ∑ b, cost v b (ω b) ≤ t₁) ∧
        (∀ (S : Finset (OddRole5 n)) (o : OddRole5 n → O), S.card ≤ n ^ 2 →
          J.pr (fun ω => ∀ b ∈ S, ω b = o b) ≤ (1 + ε n) * ∏ b ∈ S, (row b).w (o b)) := by
  obtain ⟨A, P₀, n₀, ε₀, hε₀, hclock⟩ := clock_sampling 2 2 (by norm_num)
  refine ⟨A, P₀ + 1, max n₀ 2, fun k => |ε₀ k|, ?_, ?_, ?_⟩
  · simpa using hε₀.abs
  · intro k
    exact abs_nonneg _
  · intro n hn N hNlow hNhigh O _ _ lab row cost M t₀ t₁ hcol hatom hcost hoff hmean hgap hexp
    have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : 0 < n := by omega
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hnR_sq : (n : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
      have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        calc
          (n : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast (Nat.le_mul_self n)
          _ = (n : ℝ) ^ 2 := by simp [pow_two]
      simpa using hsq
    have hM : 0 ≤ M := by
      obtain ⟨v⟩ := evenRole5_nonempty hnpos
      obtain ⟨b, _⟩ := oddAdjSet5_nonempty v hnpos
      have hO : Nonempty O := by
        by_contra hno
        haveI : IsEmpty O := not_nonempty_iff.mp hno
        have hs := (row b).sum_eq_one
        simp at hs
      obtain ⟨o⟩ := hO
      exact le_trans (hcost v b o).1 (hcost v b o).2
    have hNpos : 0 < (N : ℝ) := by
      have hpow : 0 < (2 : ℝ) ^ n := by positivity
      exact lt_of_lt_of_le hpow (by exact_mod_cast hNlow)
    have hNbound : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by
      exact_mod_cast hNhigh
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) := Real.log_le_self hnR.le
    have hlog : Real.log (N : ℝ) ≤ 2 * (n : ℝ) := by
      calc
        Real.log (N : ℝ) ≤ Real.log ((n : ℝ) * (2 : ℝ) ^ n) :=
          Real.log_le_log hNpos hNbound
        _ = Real.log (n : ℝ) + (n : ℝ) * Real.log (2 : ℝ) := by
          rw [Real.log_mul hnR.ne' (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), Real.log_pow]
        _ ≤ (n : ℝ) + (n : ℝ) := by
          apply add_le_add hlogn
          calc
            (n : ℝ) * Real.log (2 : ℝ) ≤ (n : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hlog2 hnR.le
            _ = (n : ℝ) := by ring
        _ = 2 * (n : ℝ) := by ring
    let fail : EvenRole5 n → (OddRole5 n → O) → Prop := fun v ω =>
      t₁ < ∑ b, cost v b (ω b)
    have hdep : ∀ v : EvenRole5 n, FinProb.DependsOn (fail v) (oddAdjSet5 v) := by
      intro v ω ω' hsame
      change (t₁ < ∑ b, cost v b (ω b)) = (t₁ < ∑ b, cost v b (ω' b))
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      by_cases hadj : (cube n).Adj v.1 b.1
      · have hbS : b ∈ oddAdjSet5 v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
        rw [hsame b hbS]
      · rw [hoff v b (ω b) hadj, hoff v b (ω' b) hadj]
    have hscope : ∀ v : EvenRole5 n, ((oddAdjSet5 (n := n) v).card : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
      intro v
      have hc : ((oddAdjSet5 v).card : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast oddAdjSet5_card_le v
      exact hc.trans hnR_sq
    have hinc : ∀ b : OddRole5 n, ((Finset.univ.filter (fun v : EvenRole5 n => b ∈ oddAdjSet5 v)).card : ℝ) ≤
        (n : ℝ) ^ (2 : ℝ) := by
      intro b
      have hcNat : (oddAdjIncidence5 (n := n) b).card ≤ n := oddAdjIncidence5_card_le b
      have hc : ((Finset.univ.filter (fun v : EvenRole5 n => b ∈ oddAdjSet5 v)).card : ℝ) ≤
          (n : ℝ) := by
        have heq : Finset.univ.filter (fun v : EvenRole5 n => b ∈ oddAdjSet5 v) =
            oddAdjIncidence5 b := rfl
        rw [heq]
        exact_mod_cast hcNat
      exact hc.trans hnR_sq
    have hfail : ∀ v : EvenRole5 n, (FinProb.pi row).pr (fail v) ≤ (n : ℝ) ^ (-P₀) := by
      intro v
      change (FinProb.pi row).pr (fun ω => t₁ < ∑ b, cost v b (ω b)) ≤ (n : ℝ) ^ (-P₀)
      exact product_bad_cost_prob5 hn2 row cost M t₀ t₁ P₀ hM hcost hoff hmean hgap hexp v
    obtain ⟨J, hJgood, hJjoint⟩ := hclock n hn0 N hlog (fun _ o => lab o) row fail
      (oddAdjSet5 (n := n))
      hcol hatom hdep hscope hinc hfail
    refine ⟨J, ?_, ?_⟩
    · intro ω hω
      obtain ⟨hInjective, hAvoid⟩ := hJgood ω hω
      refine ⟨hInjective, ?_⟩
      intro v
      exact le_of_not_gt (hAvoid v)
    · intro S o hS
      have hSreal : (S.card : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
        have hc : (S.card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hS
        simpa using hc
      have hprod : 0 ≤ ∏ b ∈ S, (row b).w (o b) :=
        Finset.prod_nonneg fun b hb => (row b).nonneg (o b)
      calc
        J.pr (fun ω => ∀ b ∈ S, ω b = o b) ≤
            (1 + ε₀ n) * ∏ b ∈ S, (row b).w (o b) := hJjoint S o hSreal
        _ ≤ (1 + |ε₀ n|) * ∏ b ∈ S, (row b).w (o b) := by
          exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self (ε₀ n)]) hprod


end HypercubeRamsey
