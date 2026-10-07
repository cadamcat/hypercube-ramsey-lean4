import HypercubeRamsey.Tools.Binomial_p_tools_binom

/-!
# Binomial and entropy estimates

Finite statements for central binomial atoms, consecutive half-binomial bins, binomial tails, and binary
entropy volume bounds. `Real.binEntropy` is Mathlib's natural-log binary entropy.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- Mass at `k` for a `Binomial(ell, 1/2)` random variable. -/
noncomputable def halfBinomialMass (ell : ℕ) (k : Fin (ell + 1)) : ℝ :=
  (Nat.choose ell k.val : ℝ) / (2 : ℝ) ^ ell

/-- X-Binomial: binomial coefficients are symmetric about the middle. -/
theorem binomial_choose_symm (ell k : ℕ) (hk : k ≤ ell) :
    Nat.choose ell k = Nat.choose ell (ell - k) := by
  exact (Nat.choose_symm hk).symm

/-- X-Binomial: the largest binomial coefficient is central. -/
theorem binomial_choose_le_central (ell k : ℕ) (hk : k ≤ ell) :
    Nat.choose ell k ≤ Nat.choose ell (ell / 2) := by
  exact Nat.choose_le_middle k ell

/-- X-CentralBinomUpper: every atom of `Binomial(ell, 1/2)` is at most `2 / sqrt(ell)`. -/
theorem centralBinomialUpper (ell : ℕ) (hell : 0 < ell) (k : ℕ) (hk : k ≤ ell) :
    (Nat.choose ell k : ℝ) / (2 : ℝ) ^ ell ≤ 2 / Real.sqrt ell := by
  have hEvenStrong (m : ℕ) : 0 < m →
      (Nat.centralBinom m : ℝ) / (2 : ℝ) ^ (2 * m) ≤ 1 / Real.sqrt (m + 1) := by
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro hm
      by_cases hm0 : m = 0
      · subst m
        have hs : Real.sqrt (2 : ℝ) ≤ 2 := by
          apply le_of_sq_le_sq
          · rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num
          · norm_num
        norm_num [Nat.centralBinom]
        simpa [one_div] using one_div_le_one_div_of_le
          (Real.sqrt_pos.2 (by norm_num)) hs
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        have hprev := ih hmpos
        have hrecNat := Nat.succ_mul_centralBinom_succ m
        have hrecReal : ((m + 1 : ℕ) : ℝ) * (Nat.centralBinom (m + 1) : ℝ) =
            2 * ((2 * m + 1 : ℕ) : ℝ) * (Nat.centralBinom m : ℝ) := by
          exact_mod_cast hrecNat
        have hpow : (2 : ℝ) ^ (2 * (m + 1)) = 4 * (2 : ℝ) ^ (2 * m) := by
          rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
          ring
        have hratio :
            (Nat.centralBinom (m + 1) : ℝ) / (2 : ℝ) ^ (2 * (m + 1)) =
              (((2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)) *
                ((Nat.centralBinom m : ℝ) / (2 : ℝ) ^ (2 * m))) := by
          rw [hpow]
          field_simp
          push_cast at hrecReal
          nlinarith [hrecReal]
        have hd : 0 < 2 * (m : ℝ) + 2 := by positivity
        let r : ℝ := (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2)
        have hr0 : 0 ≤ r := by dsimp [r]; positivity
        have hr2 : r ^ 2 ≤ ((m : ℝ) + 1) / ((m : ℝ) + 2) := by
          dsimp [r]
          rw [div_pow]
          apply (div_le_div_iff₀ (sq_pos_of_pos hd) (by positivity)).2
          nlinarith
        have hsx : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 :=
          Real.sq_sqrt (by positivity)
        have hsy : Real.sqrt ((m : ℝ) + 2) ^ 2 = (m : ℝ) + 2 :=
          Real.sq_sqrt (by positivity)
        have hprod : r * Real.sqrt ((m : ℝ) + 2) ≤ Real.sqrt ((m : ℝ) + 1) := by
          have hsq : (r * Real.sqrt ((m : ℝ) + 2)) ^ 2 ≤
              Real.sqrt ((m : ℝ) + 1) ^ 2 := by
            rw [mul_pow, hsy]
            have := mul_le_mul_of_nonneg_right hr2 (by positivity : 0 ≤ (m : ℝ) + 2)
            have heq : ((m : ℝ) + 1) / ((m : ℝ) + 2) * ((m : ℝ) + 2) = (m : ℝ) + 1 := by
              field_simp
            rw [heq] at this
            rw [hsx]
            exact this
          exact le_of_sq_le_sq hsq (Real.sqrt_nonneg _)
        have hratioBound : r * (1 / Real.sqrt ((m : ℝ) + 1)) ≤
            1 / Real.sqrt ((m : ℝ) + 2) := by
          have hx : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
          have hy : 0 < Real.sqrt ((m : ℝ) + 2) := Real.sqrt_pos.2 (by positivity)
          rw [show r * (1 / Real.sqrt ((m : ℝ) + 1)) = r / Real.sqrt ((m : ℝ) + 1) by ring]
          have hprod' : r * Real.sqrt ((m : ℝ) + 2) ≤ 1 * Real.sqrt ((m : ℝ) + 1) := by simpa using hprod
          exact (div_le_div_iff₀ hx hy).2 hprod'
        rw [hratio]
        calc
          r * ((Nat.centralBinom m : ℝ) / (2 : ℝ) ^ (2 * m)) ≤ r * (1 / Real.sqrt (m + 1)) :=
            mul_le_mul_of_nonneg_left hprev hr0
          _ = r * (1 / Real.sqrt ((m : ℝ) + 1)) := by norm_num
          _ ≤ 1 / Real.sqrt ((m : ℝ) + 2) := hratioBound
          _ = 1 / Real.sqrt ((m + 1 : ℕ) + 1) := by
            congr 2
            push_cast
            ring
  have hEven (m : ℕ) (hm : 0 < m) :
      (Nat.centralBinom m : ℝ) / (2 : ℝ) ^ (2 * m) ≤ 2 / Real.sqrt (2 * m) := by
    have hs := hEvenStrong m hm
    have hroot : Real.sqrt (2 * (m : ℝ)) ≤ 2 * Real.sqrt ((m : ℝ) + 1) := by
      apply le_of_sq_le_sq
      · rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
        nlinarith
      · positivity
    calc
      (Nat.centralBinom m : ℝ) / (2 : ℝ) ^ (2 * m) ≤ 1 / Real.sqrt ((m : ℝ) + 1) := hs
      _ ≤ 2 / Real.sqrt (2 * (m : ℝ)) := by
        apply (div_le_div_iff₀ (Real.sqrt_pos.2 (by positivity))
          (Real.sqrt_pos.2 (by positivity))).2
        nlinarith
  have hcentral : (Nat.choose ell (ell / 2) : ℝ) / (2 : ℝ) ^ ell ≤
      2 / Real.sqrt ell := by
    rcases Nat.even_or_odd' ell with ⟨m, rfl | rfl⟩
    ·
      have hmpos : 0 < m := by omega
      have h := hEven m hmpos
      simpa [Nat.centralBinom] using h
    ·
      have hcoef : Nat.choose (2 * m + 2) (m + 1) =
          2 * Nat.choose (2 * m + 1) m := by
        rw [Nat.choose_succ_succ]
        have hsymm : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
          have hs := Nat.choose_symm (by omega : m ≤ 2 * m + 1)
          simpa [show 2 * m + 1 - m = m + 1 by omega] using hs
        rw [hsymm]
        ring
      have h := hEven (m + 1) (by omega)
      have hmass : (Nat.choose (2 * m + 1) m : ℝ) / (2 : ℝ) ^ (2 * m + 1) =
          (Nat.choose (2 * m + 2) (m + 1) : ℝ) / (2 : ℝ) ^ (2 * m + 2) := by
        rw [hcoef]
        have hpow1 : (2 : ℝ) ^ (2 * m + 1) = (2 : ℝ) ^ (2 * m) * 2 := by
          rw [pow_succ]
        have hpow2 : (2 : ℝ) ^ (2 * m + 2) = (2 : ℝ) ^ (2 * m) * 4 := by
          rw [pow_add]
          norm_num
        rw [hpow1, hpow2]
        field_simp
        push_cast
        ring
      have hcmp : 2 / Real.sqrt (2 * (m + 1 : ℕ)) ≤
          2 / Real.sqrt (2 * m + 1 : ℕ) := by
        apply (div_le_div_iff₀ (Real.sqrt_pos.2 (by positivity))
          (Real.sqrt_pos.2 (by positivity))).2
        have hNat : 2 * m + 1 ≤ 2 * (m + 1) := by omega
        have hs := Real.sqrt_le_sqrt (show (2 * m + 1 : ℝ) ≤ (2 * (m + 1) : ℝ) by exact_mod_cast hNat)
        have hs' := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2)
        simpa using hs'
      have hdiv : (2 * m + 1) / 2 = m := by omega
      have hoddMass : (Nat.choose (2 * m + 1) ((2 * m + 1) / 2) : ℝ) /
          (2 : ℝ) ^ (2 * m + 1) =
          (Nat.choose (2 * m + 2) (m + 1) : ℝ) / (2 : ℝ) ^ (2 * m + 2) := by
        simpa [hdiv] using hmass
      calc
        (Nat.choose (2 * m + 1) ((2 * m + 1) / 2) : ℝ) /
            (2 : ℝ) ^ (2 * m + 1) =
            (Nat.choose (2 * m + 2) (m + 1) : ℝ) / (2 : ℝ) ^ (2 * m + 2) := hoddMass
        _ ≤ 2 / Real.sqrt (2 * (m + 1 : ℕ)) := by
          simpa [Nat.centralBinom, Nat.mul_add] using h
        _ ≤ 2 / Real.sqrt (2 * m + 1 : ℕ) := hcmp
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.choose_le_middle k ell)) (by positivity)).trans hcentral

/-- X-BinomEntropy: the lower binomial layers have total size at most `exp(n H_bin(rho))`. -/
theorem binomialEntropyBound (n : ℕ) (rho : ℝ) (hrho0 : 0 ≤ rho) (hrho : rho ≤ 1 / 2) :
    ∑ k ∈ (Finset.univ.filter (fun k : Fin (n + 1) => (k.val : ℝ) ≤ rho * n)),
      (Nat.choose n k.val : ℝ) ≤ Real.exp (Real.binEntropy rho * n) := by
  classical
  by_cases hrhoZ : rho = 0
  · subst rho
    have hfilter : (Finset.univ.filter
        (fun k : Fin (n + 1) => (k.val : ℝ) ≤ 0)) = {0} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hk
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero (by exact_mod_cast hk)
      · intro hk
        subst k
        simp
    simp only [zero_mul]
    rw [hfilter]
    simp [Nat.choose_zero_right, Real.binEntropy_zero]
  · have hrhoPos : 0 < rho := lt_of_le_of_ne hrho0 (Ne.symm hrhoZ)
    have honePos : 0 < 1 - rho := by linarith
    have hrhoLeOneMinus : rho ≤ 1 - rho := by linarith
    have hlogrho : Real.log rho ≤ Real.log (1 - rho) :=
      Real.log_le_log hrhoPos hrhoLeOneMinus
    have hEntropy : Real.binEntropy rho =
        -rho * Real.log rho - (1 - rho) * Real.log (1 - rho) := by
      simp [Real.binEntropy, Real.log_inv]
      ring
    let S := Finset.univ.filter (fun k : Fin (n + 1) => (k.val : ℝ) ≤ rho * n)
    have hkn (k : Fin (n + 1)) : k.val ≤ n := Nat.le_of_lt_succ k.isLt
    have hcastSub (k : Fin (n + 1)) : ((n - k.val : ℕ) : ℝ) = (n : ℝ) - k.val :=
      Nat.cast_sub (hkn k)
    have hweight (k : Fin (n + 1)) (hk : k ∈ S) :
        Real.exp (-Real.binEntropy rho * n) ≤
          rho ^ k.val * (1 - rho) ^ (n - k.val) := by
      have hk' : (k.val : ℝ) ≤ rho * n := (Finset.mem_filter.mp hk).2
      have hprod : 0 ≤ ((k.val : ℝ) - rho * n) *
          (Real.log rho - Real.log (1 - rho)) :=
        mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hk') (sub_nonpos.mpr hlogrho)
      have hlogCompare : -Real.binEntropy rho * n ≤
          (k.val : ℝ) * Real.log rho + ((n - k.val : ℕ) : ℝ) * Real.log (1 - rho) := by
        rw [hEntropy]
        rw [hcastSub k]
        push_cast
        nlinarith [hprod]
      have hlogWeight : Real.log (rho ^ k.val * (1 - rho) ^ (n - k.val)) =
          (k.val : ℝ) * Real.log rho + ((n - k.val : ℕ) : ℝ) * Real.log (1 - rho) := by
        rw [Real.log_mul (pow_pos hrhoPos _).ne' (pow_pos honePos _).ne',
          Real.log_pow, Real.log_pow]
      calc
        Real.exp (-Real.binEntropy rho * n) ≤
            Real.exp (Real.log (rho ^ k.val * (1 - rho) ^ (n - k.val))) :=
          Real.exp_le_exp.mpr (by rw [hlogWeight]; exact hlogCompare)
        _ = rho ^ k.val * (1 - rho) ^ (n - k.val) :=
          Real.exp_log (mul_pos (pow_pos hrhoPos _) (pow_pos honePos _))
    have htotal :
        (∑ k : Fin (n + 1), (Nat.choose n k.val : ℝ) *
          rho ^ k.val * (1 - rho) ^ (n - k.val)) = 1 := by
      let f : ℕ → ℝ := fun i => (Nat.choose n i : ℝ) * rho ^ i * (1 - rho) ^ (n - i)
      change (∑ k : Fin (n + 1), f k.val) = 1
      rw [Fin.sum_univ_eq_sum_range f (n + 1)]
      simpa [f, mul_assoc, mul_comm, mul_left_comm] using (add_pow rho (1 - rho) n).symm
    have hweighted :
        (∑ k ∈ S, (Nat.choose n k.val : ℝ) *
          rho ^ k.val * (1 - rho) ^ (n - k.val)) ≤ 1 := by
      calc
        (∑ k ∈ S, (Nat.choose n k.val : ℝ) *
            rho ^ k.val * (1 - rho) ^ (n - k.val)) ≤
          ∑ k : Fin (n + 1), (Nat.choose n k.val : ℝ) *
            rho ^ k.val * (1 - rho) ^ (n - k.val) := by
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
                (by intros; positivity)
        _ = 1 := htotal
    have hscaled :
        (∑ k ∈ S, (Nat.choose n k.val : ℝ) * Real.exp (-Real.binEntropy rho * n)) ≤ 1 := by
      calc
        (∑ k ∈ S, (Nat.choose n k.val : ℝ) * Real.exp (-Real.binEntropy rho * n)) ≤
          ∑ k ∈ S, (Nat.choose n k.val : ℝ) *
            (rho ^ k.val * (1 - rho) ^ (n - k.val)) := by
              apply Finset.sum_le_sum
              intro k hk
              exact mul_le_mul_of_nonneg_left (hweight k hk) (Nat.cast_nonneg _)
        _ ≤ 1 := by simpa [mul_assoc] using hweighted
    have hfactor :
        (∑ k ∈ S, (Nat.choose n k.val : ℝ)) * Real.exp (-Real.binEntropy rho * n) ≤ 1 := by
      simpa [Finset.sum_mul] using hscaled
    have hfinal :
        (∑ k ∈ S, (Nat.choose n k.val : ℝ)) ≤ Real.exp (Real.binEntropy rho * n) := by
      calc
        (∑ k ∈ S, (Nat.choose n k.val : ℝ)) =
            ((∑ k ∈ S, (Nat.choose n k.val : ℝ)) *
              Real.exp (-Real.binEntropy rho * n)) * Real.exp (Real.binEntropy rho * n) := by
                rw [mul_assoc, ← Real.exp_add]
                simp
        _ ≤ 1 * Real.exp (Real.binEntropy rho * n) :=
          mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)
        _ = Real.exp (Real.binEntropy rho * n) := one_mul _
    simpa [S] using hfinal

/-- F-BinomTail: upper additive tail of a finite `Binomial(m,p)` law. -/
noncomputable def binomialMass (m : ℕ) (p : ℝ) (k : Fin (m + 1)) : ℝ :=
  (Nat.choose m k.val : ℝ) * p ^ k.val * (1 - p) ^ (m - k.val)

/-- F-BinomTail: Hoeffding's upper-tail bound for a binomial count. -/
theorem binomialTailUpper (m : ℕ) (hm : 0 < m) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ∑ k ∈ (Finset.univ.filter
      (fun k : Fin (m + 1) => (m : ℝ) * p + t ≤ k.val)), binomialMass m p k ≤
        Real.exp (-2 * t ^ 2 / m) := by
  classical
  let theta : ℝ := 4 * t / m
  have hbernoulli := bernoulliHoeffdingMGF p theta hp0 hp1
  have hExpNat (x : ℝ) (j : ℕ) : Real.exp (x * (j : ℝ)) = Real.exp x ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.cast_succ]
      calc
        Real.exp (x * ((j : ℝ) + 1)) = Real.exp (x * (j : ℝ) + x) := by congr 1 <;> ring
        _ = Real.exp (x * (j : ℝ)) * Real.exp x := Real.exp_add _ _
        _ = Real.exp x ^ j * Real.exp x := by rw [ih]
        _ = Real.exp x ^ (j + 1) := by rw [pow_succ]
  let A : ℝ := p * Real.exp theta
  let C : ℝ := Real.exp (-theta * p)
  let f : ℕ → ℝ := fun i => (Nat.choose m i : ℝ) * p ^ i * (1 - p) ^ (m - i) *
    Real.exp (theta * ((i : ℝ) - (m : ℝ) * p))
  have hterm (i : ℕ) (hi : i ≤ m) : f i =
      C ^ m * ((Nat.choose m i : ℝ) * A ^ i * (1 - p) ^ (m - i)) := by
    have hexp : Real.exp (theta * ((i : ℝ) - (m : ℝ) * p)) =
        C ^ m * Real.exp theta ^ i := by
      rw [show theta * ((i : ℝ) - (m : ℝ) * p) = (-theta * p) * (m : ℝ) + theta * (i : ℝ) by ring,
        Real.exp_add, hExpNat (-theta * p) m, hExpNat theta i]
    have hpowers : p ^ i * Real.exp theta ^ i = (p * Real.exp theta) ^ i := by
      rw [← mul_pow]
    dsimp [f, A, C]
    rw [hexp]
    calc
      (Nat.choose m i : ℝ) * p ^ i * (1 - p) ^ (m - i) *
          (Real.exp (-theta * p) ^ m * Real.exp theta ^ i) =
        Real.exp (-theta * p) ^ m *
          ((Nat.choose m i : ℝ) * (p ^ i * Real.exp theta ^ i) * (1 - p) ^ (m - i)) := by ring
      _ = Real.exp (-theta * p) ^ m *
          ((Nat.choose m i : ℝ) * (p * Real.exp theta) ^ i * (1 - p) ^ (m - i)) := by rw [hpowers]
  have htotal :
      (∑ k : Fin (m + 1), binomialMass m p k *
        Real.exp (theta * ((k.val : ℝ) - (m : ℝ) * p))) =
          (C * ((1 - p) + A)) ^ m := by
    change (∑ k : Fin (m + 1), f k.val) = _
    rw [Fin.sum_univ_eq_sum_range f (m + 1)]
    calc
      (∑ i ∈ Finset.range (m + 1), f i) =
          ∑ i ∈ Finset.range (m + 1),
            C ^ m * ((Nat.choose m i : ℝ) * A ^ i * (1 - p) ^ (m - i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hterm i (by simp only [Finset.mem_range] at hi; omega)
      _ = C ^ m * (∑ i ∈ Finset.range (m + 1),
            (Nat.choose m i : ℝ) * A ^ i * (1 - p) ^ (m - i)) := by rw [← Finset.mul_sum]
      _ = C ^ m * ((1 - p) + A) ^ m := by
            congr 1
            simpa [mul_assoc, mul_comm, mul_left_comm, add_comm] using (add_pow A (1 - p) m).symm
      _ = (C * ((1 - p) + A)) ^ m := by rw [mul_pow]
  have hcentered :
      (∑ k : Fin (m + 1), binomialMass m p k *
        Real.exp (theta * ((k.val : ℝ) - (m : ℝ) * p))) ≤
          Real.exp ((m : ℝ) * theta ^ 2 / 8) := by
    calc
      (∑ k : Fin (m + 1), binomialMass m p k *
          Real.exp (theta * ((k.val : ℝ) - (m : ℝ) * p))) =
        (C * ((1 - p) + A)) ^ m := htotal
      _ ≤ Real.exp (theta ^ 2 / 8) ^ m := by
        exact pow_le_pow_left₀ (by positivity : 0 ≤ C * ((1 - p) + A)) hbernoulli m
      _ = Real.exp ((m : ℝ) * theta ^ 2 / 8) := by
        rw [← hExpNat (theta ^ 2 / 8) m]
        congr 1
        ring
  let S := Finset.univ.filter (fun k : Fin (m + 1) => (m : ℝ) * p + t ≤ k.val)
  have htheta : 0 ≤ theta := by dsimp [theta]; positivity
  have htailScaled : Real.exp (theta * t) * (∑ k ∈ S, binomialMass m p k) ≤
      Real.exp ((m : ℝ) * theta ^ 2 / 8) := by
    calc
      Real.exp (theta * t) * (∑ k ∈ S, binomialMass m p k) =
          ∑ k ∈ S, binomialMass m p k * Real.exp (theta * t) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ ≤ ∑ k ∈ S, binomialMass m p k *
          Real.exp (theta * ((k.val : ℝ) - (m : ℝ) * p)) := by
            apply Finset.sum_le_sum
            intro k hk
            have hk' : (m : ℝ) * p + t ≤ k.val := (Finset.mem_filter.mp hk).2
            have harg : theta * t ≤ theta * ((k.val : ℝ) - (m : ℝ) * p) := by
              apply mul_le_mul_of_nonneg_left _ htheta
              linarith
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by
              unfold binomialMass
              positivity)
      _ ≤ ∑ k : Fin (m + 1), binomialMass m p k *
          Real.exp (theta * ((k.val : ℝ) - (m : ℝ) * p)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (by
              intro k hk hkuniv
              unfold binomialMass
              positivity)
      _ ≤ Real.exp ((m : ℝ) * theta ^ 2 / 8) := hcentered
  have hbound : (∑ k ∈ S, binomialMass m p k) ≤
      Real.exp ((m : ℝ) * theta ^ 2 / 8) / Real.exp (theta * t) :=
    (le_div_iff₀ (Real.exp_pos _)).2 (by simpa [mul_comm] using htailScaled)
  have hexp : (Real.exp ((m : ℝ) * theta ^ 2 / 8) / Real.exp (theta * t)) =
      Real.exp (-theta * t + (m : ℝ) * theta ^ 2 / 8) := by
    rw [← Real.exp_sub]
    congr 1 <;> ring
  have hopt : -theta * t + (m : ℝ) * theta ^ 2 / 8 = -2 * t ^ 2 / m := by
    dsimp [theta]
    field_simp [Nat.cast_ne_zero.mpr hm.ne']
    ring
  rw [hexp, hopt] at hbound
  simpa [S] using hbound

/-- F-BinomTail: Hoeffding's lower-tail bound for a finite binomial count. -/
theorem binomialTailLower (m : ℕ) (hm : 0 < m) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ∑ k ∈ (Finset.univ.filter
      (fun k : Fin (m + 1) => (k.val : ℝ) ≤ (m : ℝ) * p - t)), binomialMass m p k ≤
        Real.exp (-2 * t ^ 2 / m) := by
  classical
  let theta : ℝ := -4 * t / m
  have hbernoulli := bernoulliHoeffdingMGF p theta hp0 hp1
  have hExpNat (x : ℝ) (j : ℕ) : Real.exp (x * (j : ℝ)) = Real.exp x ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.cast_succ]
      calc
        Real.exp (x * ((j : ℝ) + 1)) = Real.exp (x * (j : ℝ) + x) := by congr 1 <;> ring
        _ = Real.exp (x * (j : ℝ)) * Real.exp x := Real.exp_add _ _
        _ = Real.exp x ^ j * Real.exp x := by rw [ih]
        _ = Real.exp x ^ (j + 1) := by rw [pow_succ]
  let A : ℝ := p * Real.exp theta
  let C : ℝ := Real.exp (-theta * p)
  let f : ℕ → ℝ := fun i => (Nat.choose m i : ℝ) * p ^ i * (1 - p) ^ (m - i) *
    Real.exp (theta * ((i : ℝ) - (m : ℝ) * p))
  have hterm (i : ℕ) (hi : i ≤ m) : f i =
      C ^ m * ((Nat.choose m i : ℝ) * A ^ i * (1 - p) ^ (m - i)) := by
    have hexp : Real.exp (theta * ((i : ℝ) - (m : ℝ) * p)) =
        C ^ m * Real.exp theta ^ i := by
      rw [show theta * ((i : ℝ) - (m : ℝ) * p) = (-theta * p) * (m : ℝ) + theta * (i : ℝ) by ring,
        Real.exp_add, hExpNat (-theta * p) m, hExpNat theta i]
    have hpowers : p ^ i * Real.exp theta ^ i = (p * Real.exp theta) ^ i := by
      rw [← mul_pow]
    dsimp [f, A, C]
    rw [hexp]
    calc
      (Nat.choose m i : ℝ) * p ^ i * (1 - p) ^ (m - i) *
          (Real.exp (-theta * p) ^ m * Real.exp theta ^ i) =
        Real.exp (-theta * p) ^ m *
          ((Nat.choose m i : ℝ) * (p ^ i * Real.exp theta ^ i) * (1 - p) ^ (m - i)) := by ring
      _ = Real.exp (-theta * p) ^ m *
          ((Nat.choose m i : ℝ) * (p * Real.exp theta) ^ i * (1 - p) ^ (m - i)) := by rw [hpowers]
  have htotal :
      (∑ k : Fin (m + 1), binomialMass m p k *
        Real.exp (theta * ((k.val : ℝ) - (m : ℝ) * p))) =
          (C * ((1 - p) + A)) ^ m := by
    change (∑ k : Fin (m + 1), f k.val) = _
    rw [Fin.sum_univ_eq_sum_range f (m + 1)]
    calc
      (∑ i ∈ Finset.range (m + 1), f i) =
          ∑ i ∈ Finset.range (m + 1),
            C ^ m * ((Nat.choose m i : ℝ) * A ^ i * (1 - p) ^ (m - i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hterm i (by simp only [Finset.mem_range] at hi; omega)
      _ = C ^ m * (∑ i ∈ Finset.range (m + 1),
            (Nat.choose m i : ℝ) * A ^ i * (1 - p) ^ (m - i)) := by rw [← Finset.mul_sum]
      _ = C ^ m * ((1 - p) + A) ^ m := by
            congr 1
            simpa [mul_assoc, mul_comm, mul_left_comm, add_comm] using (add_pow A (1 - p) m).symm
      _ = (C * ((1 - p) + A)) ^ m := by rw [mul_pow]
  have hcentered :
      (∑ k : Fin (m + 1), binomialMass m p k *
        Real.exp (theta * ((k.val : ℝ) - (m : ℝ) * p))) ≤
          Real.exp ((m : ℝ) * theta ^ 2 / 8) := by
    calc
      (∑ k : Fin (m + 1), binomialMass m p k *
          Real.exp (theta * ((k.val : ℝ) - (m : ℝ) * p))) =
        (C * ((1 - p) + A)) ^ m := htotal
      _ ≤ Real.exp (theta ^ 2 / 8) ^ m := by
        exact pow_le_pow_left₀ (by positivity : 0 ≤ C * ((1 - p) + A)) hbernoulli m
      _ = Real.exp ((m : ℝ) * theta ^ 2 / 8) := by
        rw [← hExpNat (theta ^ 2 / 8) m]
        congr 1
        ring
  let S := Finset.univ.filter (fun k : Fin (m + 1) => (k.val : ℝ) ≤ (m : ℝ) * p - t)
  have htheta : theta ≤ 0 := by
    have hnonneg : 0 ≤ 4 * t / (m : ℝ) := div_nonneg (by positivity) (by positivity)
    have heq : theta = -(4 * t / (m : ℝ)) := by dsimp [theta]; ring
    rw [heq]
    exact neg_nonpos.mpr hnonneg
  have htailScaled : Real.exp (theta * (-t)) * (∑ k ∈ S, binomialMass m p k) ≤
      Real.exp ((m : ℝ) * theta ^ 2 / 8) := by
    calc
      Real.exp (theta * (-t)) * (∑ k ∈ S, binomialMass m p k) =
          ∑ k ∈ S, binomialMass m p k * Real.exp (theta * (-t)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ ≤ ∑ k ∈ S, binomialMass m p k *
          Real.exp (theta * ((k.val : ℝ) - (m : ℝ) * p)) := by
            apply Finset.sum_le_sum
            intro k hk
            have hk' : (k.val : ℝ) ≤ (m : ℝ) * p - t := (Finset.mem_filter.mp hk).2
            have harg : theta * (-t) ≤ theta * ((k.val : ℝ) - (m : ℝ) * p) := by
              apply mul_le_mul_of_nonpos_left _ htheta
              linarith
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by
              unfold binomialMass
              positivity)
      _ ≤ ∑ k : Fin (m + 1), binomialMass m p k *
          Real.exp (theta * ((k.val : ℝ) - (m : ℝ) * p)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (by
              intro k hk hkuniv
              unfold binomialMass
              positivity)
      _ ≤ Real.exp ((m : ℝ) * theta ^ 2 / 8) := hcentered
  have hbound : (∑ k ∈ S, binomialMass m p k) ≤
      Real.exp ((m : ℝ) * theta ^ 2 / 8) / Real.exp (theta * (-t)) :=
    (le_div_iff₀ (Real.exp_pos _)).2 (by simpa [mul_comm] using htailScaled)
  have hexp : (Real.exp ((m : ℝ) * theta ^ 2 / 8) / Real.exp (theta * (-t))) =
      Real.exp (theta * t + (m : ℝ) * theta ^ 2 / 8) := by
    rw [← Real.exp_sub]
    congr 1 <;> ring
  have hopt : theta * t + (m : ℝ) * theta ^ 2 / 8 = -2 * t ^ 2 / m := by
    dsimp [theta]
    field_simp [Nat.cast_ne_zero.mpr hm.ne']
    ring
  rw [hexp, hopt] at hbound
  simpa [S] using hbound

/-- F-Bins: a consecutive interval of binomial weights used as one coarse bin. -/
def IsConsecutiveBin {ell : ℕ} (B : Finset (Fin (ell + 1))) : Prop :=
  ∃ a b : ℕ, ∀ k, k ∈ B ↔ a ≤ k.val ∧ k.val ≤ b

/-- F-Bins: partition `{0,…,ell}` into consecutive intervals, each of half-binomial mass at most `2ε`;
the greedy packing can be chosen with at most `ε⁻¹+1` intervals. -/
theorem exists_consecutive_bin_partition (ell : ℕ) (hell : 0 < ell) (ε : ℝ)
    (hε : 2 / Real.sqrt ell ≤ ε) :
    ∃ bins : Finset (Finset (Fin (ell + 1))),
      (∀ k, ∃! B, B ∈ bins ∧ k ∈ B) ∧
      (∀ B, B ∈ bins → IsConsecutiveBin B ∧
        ∑ k ∈ B, halfBinomialMass ell k ≤ 2 * ε) ∧
      (bins.card : ℝ) ≤ ε⁻¹ + 1 := by
  classical
  have hεpos : 0 < ε := by
    have hsqrt : 0 < Real.sqrt (ell : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hell)
    exact lt_of_lt_of_le (div_pos (by norm_num) hsqrt) hε
  let w : Fin (ell + 1) → ℝ := halfBinomialMass ell
  have hw_nonneg (k : Fin (ell + 1)) : 0 ≤ w k := by
    dsimp [w, halfBinomialMass]
    positivity
  have hw_le (k : Fin (ell + 1)) : w k ≤ ε := by
    have h := centralBinomialUpper ell hell k.val (Nat.le_of_lt_succ k.isLt)
    simpa [w, halfBinomialMass] using h.trans hε
  let wNat : ℕ → ℝ := fun i => if hi : i < ell + 1 then w ⟨i, hi⟩ else 0
  have hwNat_nonneg (i : ℕ) : 0 ≤ wNat i := by
    dsimp [wNat]
    split_ifs with hi
    · exact hw_nonneg _
    · positivity
  have hwNat_le (i : ℕ) (hi : i ≤ ell) : wNat i ≤ ε := by
    have hlt : i < ell + 1 := by omega
    have heq : wNat i = w ⟨i, hlt⟩ := by
      dsimp [wNat]
      split_ifs <;> simp_all
    rw [heq]
    exact hw_le _
  have hchoose :
      (∑ i ∈ Finset.range (ell + 1), (Nat.choose ell i : ℝ)) = (2 : ℝ) ^ ell := by
    exact_mod_cast Nat.sum_range_choose ell
  have htotal : (∑ k : Fin (ell + 1), w k) = 1 := by
    change (∑ k : Fin (ell + 1), (Nat.choose ell k.val : ℝ) / (2 : ℝ) ^ ell) = 1
    rw [Fin.sum_univ_eq_sum_range (fun i => (Nat.choose ell i : ℝ) / (2 : ℝ) ^ ell) (ell + 1)]
    rw [← Finset.sum_div, hchoose]
    field_simp
  let cumMass : ℕ → ℝ := fun j => ∑ i ∈ Finset.range j, wNat i
  have hprefix_nonneg (j : ℕ) : 0 ≤ cumMass j := by
    dsimp [cumMass]
    exact Finset.sum_nonneg fun i hi => hwNat_nonneg i
  have hprefix_mono : Monotone cumMass := by
    intro a b hab
    dsimp [cumMass]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (by
      intro i hi hnot
      exact hwNat_nonneg i)
  have hprefix_succ (j : ℕ) : cumMass (j + 1) = cumMass j + wNat j := by
    simp [cumMass, Finset.sum_range_succ]
  have hprefix_total : cumMass (ell + 1) = 1 := by
    dsimp [cumMass]
    have hsumRange :
        (∑ i ∈ Finset.range (ell + 1), wNat i) = ∑ k : Fin (ell + 1), w k := by
      calc
        (∑ i ∈ Finset.range (ell + 1), wNat i) =
            ∑ k : Fin (ell + 1), wNat k.val :=
              (Fin.sum_univ_eq_sum_range wNat (ell + 1)).symm
        _ = ∑ k : Fin (ell + 1), w k := by
          apply Finset.sum_congr rfl
          intro k hk
          have heq : wNat k.val = w k := by
            dsimp [wNat]
            split_ifs with h
            · rfl
            · exact (h k.isLt).elim
          exact heq
    exact hsumRange.trans htotal
  let τ : ℕ → ℕ := fun j => Nat.floor (cumMass j / ε)
  have hτ_spec (j : ℕ) :
      (τ j : ℝ) ≤ cumMass j / ε ∧ cumMass j / ε < (τ j : ℝ) + 1 := by
    have h0 : 0 ≤ cumMass j / ε := div_nonneg (hprefix_nonneg j) hεpos.le
    simpa [τ] using (Nat.floor_eq_iff h0).mp rfl
  have hτ_mono : Monotone τ := by
    intro a b hab
    dsimp [τ]
    apply Nat.floor_mono
    exact div_le_div_of_nonneg_right (hprefix_mono hab) hεpos.le
  have hτ_bound (k : Fin (ell + 1)) : τ k.val ≤ Nat.floor (1 / ε) := by
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ hεpos.le
    calc
      cumMass k.val ≤ cumMass (ell + 1) := hprefix_mono (by omega)
      _ = 1 := hprefix_total
  let tag : Fin (ell + 1) → ℕ := fun k => τ k.val
  let tags : Finset ℕ := Finset.univ.image tag
  let fiber (q : ℕ) : Finset (Fin (ell + 1)) := Finset.univ.filter (fun k => tag k = q)
  let bins : Finset (Finset (Fin (ell + 1))) := tags.image fiber
  have hfiber_nonempty (q : ℕ) (hq : q ∈ tags) : (fiber q).Nonempty := by
    rcases Finset.mem_image.mp hq with ⟨k, hk, rfl⟩
    exact ⟨k, by simp [fiber, tag]⟩
  have hfiber_interval (q : ℕ) (hq : q ∈ tags) :
      ∀ k : Fin (ell + 1), k ∈ fiber q ↔
        ((fiber q).min' (hfiber_nonempty q hq)).val ≤ k.val ∧
          k.val ≤ ((fiber q).max' (hfiber_nonempty q hq)).val := by
    let hn := hfiber_nonempty q hq
    let a := (fiber q).min' hn
    let b := (fiber q).max' hn
    have ha : a ∈ fiber q := Finset.min'_mem _ _
    have hb : b ∈ fiber q := Finset.max'_mem _ _
    have hta : τ a.val = q := (Finset.mem_filter.mp ha).2
    have htb : τ b.val = q := (Finset.mem_filter.mp hb).2
    intro k
    constructor
    · intro hk
      have hak := Finset.min'_le (fiber q) k hk
      have hkb := Finset.le_max' (fiber q) k hk
      exact ⟨by exact_mod_cast hak, by exact_mod_cast hkb⟩
    · intro hk
      have hleft := hτ_mono hk.1
      have hright := hτ_mono hk.2
      rw [hta] at hleft
      rw [htb] at hright
      have htag : τ k.val = q := Nat.le_antisymm hright hleft
      have htag' : tag k = q := by simpa [tag] using htag
      simp [fiber, htag']
  have hfiber_consecutive (q : ℕ) (hq : q ∈ tags) : IsConsecutiveBin (fiber q) := by
    refine ⟨((fiber q).min' (hfiber_nonempty q hq)).val,
      ((fiber q).max' (hfiber_nonempty q hq)).val, ?_⟩
    exact hfiber_interval q hq
  have hfiber_mass (q : ℕ) (hq : q ∈ tags) :
      (∑ k ∈ fiber q, w k) ≤ 2 * ε := by
    let hn := hfiber_nonempty q hq
    let a := (fiber q).min' hn
    let b := (fiber q).max' hn
    have ha : a ∈ fiber q := Finset.min'_mem _ _
    have hb : b ∈ fiber q := Finset.max'_mem _ _
    have hta : τ a.val = q := (Finset.mem_filter.mp ha).2
    have htb : τ b.val = q := (Finset.mem_filter.mp hb).2
    have hab : a.val ≤ b.val := by exact_mod_cast Finset.min'_le (fiber q) b hb
    have hmassEq : (∑ k ∈ fiber q, w k) = cumMass (b.val + 1) - cumMass a.val := by
      rw [show fiber q = Finset.univ.filter (fun k : Fin (ell + 1) =>
          a.val ≤ k.val ∧ k.val ≤ b.val) by
            ext k
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact (hfiber_interval q hq k)]
      have hbij :
          (∑ k ∈ (Finset.univ.filter (fun k : Fin (ell + 1) =>
              a.val ≤ k.val ∧ k.val ≤ b.val)), w k) =
            ∑ i ∈ Finset.Icc a.val b.val, wNat i := by
        apply Finset.sum_bij (fun k _ => k.val)
        · intro k hk
          exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hk).2
        · intro k₁ hk₁ k₂ hk₂ heq
          exact Fin.ext heq
        · intro i hi
          let k : Fin (ell + 1) := ⟨i, by have := Finset.mem_Icc.mp hi; omega⟩
          refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mp hi⟩, ?_⟩
          rfl
        · intro k hk
          change w k = (if hi : k.val < ell + 1 then w ⟨k.val, hi⟩ else 0)
          rw [dif_pos k.isLt]
      rw [hbij]
      have hIco : Finset.Ico a.val (b.val + 1) = Finset.Icc a.val b.val := by
        ext i
        simp [Finset.mem_Ico, Finset.mem_Icc]
      rw [← hIco, Finset.sum_Ico_eq_sub _ (by omega)]
    have hlow := (hτ_spec a.val).1
    have hupp := (hτ_spec b.val).2
    have hlow' : (q : ℝ) * ε ≤ cumMass a.val := by
      rw [hta] at hlow
      exact (le_div_iff₀ hεpos).mp hlow
    have hupp' : cumMass b.val < ((q : ℝ) + 1) * ε := by
      rw [htb] at hupp
      exact (div_lt_iff₀ hεpos).mp hupp
    have hstep : cumMass (b.val + 1) ≤ cumMass b.val + ε := by
      rw [hprefix_succ]
      exact add_le_add_right (hwNat_le b.val (by omega)) (cumMass b.val)
    rw [hmassEq]
    nlinarith
  refine ⟨bins, ?_, ?_, ?_⟩
  · intro k
    let q := tag k
    have hq : q ∈ tags := Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    have hkmem : k ∈ fiber q := by simp [fiber, q]
    refine ⟨fiber q, ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, hkmem⟩, ?_⟩
    intro B hB
    rcases Finset.mem_image.mp hB.1 with ⟨q', hq', rfl⟩
    have hk : tag k = q' := (Finset.mem_filter.mp hB.2).2
    subst q'
    rfl
  · intro B hB
    rcases Finset.mem_image.mp hB with ⟨q, hq, rfl⟩
    exact ⟨hfiber_consecutive q hq, hfiber_mass q hq⟩
  · have htags : tags ⊆ Finset.range (Nat.floor (1 / ε) + 1) := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨k, hk, rfl⟩
      rw [Finset.mem_range]
      simpa [tag] using Nat.lt_succ_of_le (hτ_bound k)
    have hcardTags : tags.card ≤ Nat.floor (1 / ε) + 1 := by
      calc
        tags.card ≤ (Finset.range (Nat.floor (1 / ε) + 1)).card := Finset.card_le_card htags
        _ = Nat.floor (1 / ε) + 1 := by simp
    have hcardBins : bins.card ≤ tags.card := Finset.card_image_le
    calc
      (bins.card : ℝ) ≤ (Nat.floor (1 / ε) + 1 : ℝ) := by exact_mod_cast hcardBins.trans hcardTags
      _ = (Nat.floor (1 / ε) : ℝ) + 1 := by norm_cast
      _ ≤ ε⁻¹ + 1 := by
        have hf := Nat.floor_le (show 0 ≤ (1 : ℝ) / ε by positivity)
        simpa [one_div] using add_le_add_right hf (1 : ℝ)

end HypercubeRamsey
