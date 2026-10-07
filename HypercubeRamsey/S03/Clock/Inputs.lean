import HypercubeRamsey.S03.Clock.Leaves
import HypercubeRamsey.S03.Clock.Inputs_p_clock_r1


/-!
# Clock sampling inputs and Step 1 certificates

This file packages exactly the finite row/output/predicate data from Lemma 3.10.  `TrimCertificate` records
the discarded mass, conditional failure estimates, and the completed label columns used by the independent
edge clocks.
-/

namespace HypercubeRamsey.Clock

open scoped BigOperators

/-- The row laws, output labels, failure predicates and their scopes. -/
structure SamplingInstance (n g : ℕ) (R K : Type*)
    [Fintype R] [DecidableEq R] [Fintype K]
    (Ω : R → Type*) [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)] where
  lab : ∀ a, Ω a → Fin g
  p : ∀ a, FinProb (Ω a)
  failure : K → (∀ a, Ω a) → Prop
  scope : K → Finset R

/-- The independent product law of an instance. -/
noncomputable def SamplingInstance.productLaw {n g : ℕ} {R K : Type*}
    [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (I : SamplingInstance n g R K Ω) : FinProb (∀ a, Ω a) := FinProb.pi I.p

/-- The quantitative assumptions in the frozen clock-sampling statement. -/
def SamplingInstance.Admissible {n g : ℕ} {R K : Type*}
    [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (I : SamplingInstance n g R K Ω) (B A P : ℝ) : Prop :=
  (∀ y, ∑ a, labMarg (I.p a) (I.lab a) y ≤ 1e-8) ∧
  (∀ a y, labMarg (I.p a) (I.lab a) y ≤ (n : ℝ) ^ (-A)) ∧
  (∀ k, FinProb.DependsOn (I.failure k) (I.scope k)) ∧
  (∀ k, ((I.scope k).card : ℝ) ≤ (n : ℝ) ^ B) ∧
  (∀ a, ((Finset.univ.filter (fun k => a ∈ I.scope k)).card : ℝ) ≤ (n : ℝ) ^ B) ∧
  (∀ k, I.productLaw.pr (I.failure k) ≤ (n : ℝ) ^ (-P))

/-- A predicate's probability after one scope row has been pinned to an output. -/
noncomputable def pinnedFailureProb {R K : Type*}
    [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (laws : ∀ a, FinProb (Ω a)) (F : K → (∀ a, Ω a) → Prop)
    (k : K) (a : R) (o : Ω a) : ℝ :=
  (FinProb.pi laws).pr (fun ω => F k ω ∧ ω a = o) / (laws a).w o

/-- A certificate for Step 1: trim outputs with large pinned failure probability, renormalize, and complete
all label columns to a common rate `θ` with dummy rows. -/
structure TrimCertificate {n g : ℕ} {R K : Type*}
    [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (I : SamplingInstance n g R K Ω) (B A P : ℝ) where
  keep : ∀ a, Finset (Ω a)
  trimmed : ∀ a, FinProb (Ω a)
  trimmed_supported : ∀ a o, o ∉ keep a → (trimmed a).w o = 0
  /-- The trimmed law is the original law restricted to `keep a` and renormalized (TeX 03:825). -/
  trimmed_eq : ∀ a o, (trimmed a).w o =
    if o ∈ keep a then (I.p a).w o / (I.p a).pr (fun o' => o' ∈ keep a) else 0
  discarded_mass : ∀ a, (I.p a).pr (fun o => o ∉ keep a) ≤ (n : ℝ) ^ (B - P / 2)
  trimmed_atom : ∀ a y, labMarg (trimmed a) (I.lab a) y ≤ 2 * (n : ℝ) ^ (-A)
  trimmed_failure : ∀ k, (FinProb.pi trimmed).pr (I.failure k) ≤ (n : ℝ) ^ (-P / 3)
  trimmed_pinned_failure : ∀ k a, a ∈ I.scope k → ∀ o ∈ keep a,
    pinnedFailureProb trimmed I.failure k a o ≤ (n : ℝ) ^ (-P / 3)
  dummyRows : ℕ
  dummyLaw : Fin dummyRows → Fin g → ℝ
  dummy_nonneg : ∀ i y, 0 ≤ dummyLaw i y
  dummy_row_sum : ∀ i, ∑ y, dummyLaw i y = 1
  theta : ℝ
  theta_lower : 1e-6 ≤ theta
  theta_upper : theta ≤ 1e-6 + 1 / (g : ℝ)
  completed_card : theta * (g : ℝ) = (Fintype.card R + dummyRows : ℝ)
  completed_columns : ∀ y, (∑ a, labMarg (trimmed a) (I.lab a) y) +
    (∑ i, dummyLaw i y) = theta
  dummy_atom : ∀ i y, dummyLaw i y ≤ 2 / (g : ℝ)

set_option maxHeartbeats 1000000 in
/-- L3.10a (03:817–842): discard rare outputs, control the renormalization loss, and complete every label
column to the common rate `θ`. `P` is large in terms of `B` (03:806–807): with `n ≥ 2`, `4B + 4 ≤ P` makes the
per-row loss `n^{B-P/2} ≤ n^{-B-2} ≤ 1/4` and the loss over a scope or query `n^{2B-P/2} ≤ n^{-2} ≤ 1/4`. -/
theorem step1_trim_and_complete {n g : ℕ} {R K : Type*}
    [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (I : SamplingInstance n g R K Ω) (B A P : ℝ)
    (hn : 2 ≤ n) (hB : 0 ≤ B) (hBP : 4 * B + 4 ≤ P)
    (hI : I.Admissible B A P) : Nonempty (TrimCertificate I B A P) := by
  classical
  rcases hI with ⟨hload, hatom, hdepends, hscope, hincident, hfailure⟩
  let nR : ℝ := (n : ℝ)
  let eps : ℝ := nR ^ (-P / 2)
  let q : ℝ := nR ^ (B - P / 2)
  let x : ℝ := nR ^ (2 * B - P / 2)
  have hnR : 2 ≤ nR := by
    change (2 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hnpos : 0 < nR := lt_of_lt_of_le (by norm_num) hnR
  have hP4 : 4 ≤ P := by linarith [hBP, hB]
  have hsmallExp : B - P / 2 ≤ -B - 2 := by linarith [hBP]
  have htotalExp : 2 * B - P / 2 ≤ -2 := by linarith [hBP]
  have hnegB : -B - 2 ≤ -2 := by linarith [hB]
  have hpow2 : nR ^ (-2 : ℝ) ≤ 1 / 4 := by
    calc
      nR ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hnR (by norm_num)
      _ = 1 / 4 := by
        rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact Real.rpow_nonneg (le_of_lt hnpos) _
  have hqle : q ≤ 1 / 4 := by
    dsimp [q]
    calc
      nR ^ (B - P / 2) ≤ nR ^ (-B - 2) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [hnR]) hsmallExp
      _ ≤ nR ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith [hnR]) hnegB
      _ ≤ 1 / 4 := hpow2
  have hxle : x ≤ 1 / 4 := by
    dsimp [x]
    exact (Real.rpow_le_rpow_of_exponent_le (by linarith [hnR]) htotalExp).trans hpow2
  have hepspos : 0 < eps := by
    dsimp [eps]
    exact Real.rpow_pos_of_pos hnpos _
  have hepsSq : eps * eps = nR ^ (-P) := by
    dsimp [eps]
    calc
      nR ^ (-P / 2) * nR ^ (-P / 2) = nR ^ ((-P / 2) + (-P / 2)) :=
        (Real.rpow_add hnpos _ _).symm
      _ = nR ^ (-P) := by congr 1 <;> ring
  have hprobRatio : nR ^ (-P) / eps ≤ eps := by
    apply (div_le_iff₀ hepspos).2
    rw [← hepsSq]
  let incident : R → Finset K := fun a => Finset.univ.filter fun k => a ∈ I.scope k
  let keep : ∀ a, Finset (Ω a) := fun a => Finset.univ.filter fun o =>
    ∀ k ∈ incident a, pinnedFailureProb I.p I.failure k a o ≤ eps
  have hpinExpect (k : K) (a : R) :
      (I.p a).expect (fun o => pinnedFailureProb I.p I.failure k a o) =
        I.productLaw.pr (I.failure k) := by
    simpa [pinnedFailureProb, SamplingInstance.productLaw] using
      (pi_pinned_expect I.p (I.failure k) a)
  have hpinNonneg (k : K) (a : R) (o : Ω a) :
      0 ≤ pinnedFailureProb I.p I.failure k a o := by
    unfold pinnedFailureProb
    exact div_nonneg (finProb_pr_nonneg I.productLaw
      (fun ω => I.failure k ω ∧ ω a = o)) ((I.p a).nonneg o)
  have hbadEach (k : K) (a : R) :
      (I.p a).pr (fun o => eps < pinnedFailureProb I.p I.failure k a o) ≤ eps := by
    have hmarkov := FinProb.markov (I.p a)
      (fun o => pinnedFailureProb I.p I.failure k a o) eps
      (hpinNonneg k a) hepspos
    calc
      (I.p a).pr (fun o => eps < pinnedFailureProb I.p I.failure k a o) ≤
          (I.p a).pr (fun o => eps ≤ pinnedFailureProb I.p I.failure k a o) :=
        finProb_pr_mono (I.p a) (by intro o ho; exact le_of_lt ho)
      _ ≤ (I.p a).expect (fun o => pinnedFailureProb I.p I.failure k a o) / eps := hmarkov
      _ = I.productLaw.pr (I.failure k) / eps := by rw [← hpinExpect]
      _ ≤ nR ^ (-P) / eps := div_le_div_of_nonneg_right (hfailure k) hepspos.le
      _ ≤ eps := hprobRatio
  have hdiscardMass (a : R) :
      (I.p a).pr (fun o => o ∉ keep a) ≤ q := by
    have hbadEq : (fun o => o ∉ keep a) =
        (fun o => ∃ k ∈ incident a,
          eps < pinnedFailureProb I.p I.failure k a o) := by
      funext o
      simp [keep, not_le]
    have hUnion := finProb_pr_biUnion_le_sum (I.p a) (incident a)
      (fun k o => eps < pinnedFailureProb I.p I.failure k a o)
    have hsum :
        (∑ k ∈ incident a,
          (I.p a).pr (fun o => eps < pinnedFailureProb I.p I.failure k a o)) ≤
          (incident a).card * eps := by
      calc
        _ ≤ ∑ k ∈ incident a, eps := Finset.sum_le_sum fun k hk => hbadEach k a
        _ = (incident a).card * eps := by simp
    have hinc : ((incident a).card : ℝ) ≤ nR ^ B := by
      simpa [incident, nR] using hincident a
    have hprod : (incident a).card * eps ≤ q := by
      calc
        (incident a).card * eps ≤ nR ^ B * eps :=
          mul_le_mul_of_nonneg_right hinc hepspos.le
        _ = q := by
          dsimp [eps, q]
          calc
            nR ^ B * nR ^ (-P / 2) = nR ^ (B + (-P / 2)) :=
              (Real.rpow_add hnpos _ _).symm
            _ = nR ^ (B - P / 2) := by congr 1 <;> ring
    calc
      (I.p a).pr (fun o => o ∉ keep a) =
          (I.p a).pr (fun o => ∃ k ∈ incident a,
            eps < pinnedFailureProb I.p I.failure k a o) := by rw [hbadEq]
      _ ≤ ∑ k ∈ incident a,
          (I.p a).pr (fun o => eps < pinnedFailureProb I.p I.failure k a o) := hUnion
      _ ≤ (incident a).card * eps := hsum
      _ ≤ q := hprod
  let keepMass (a : R) : ℝ := (I.p a).pr (fun o => o ∈ keep a)
  have hkeepLower (a : R) : 1 - q ≤ keepMass a := by
    have hcompl := finProb_pr_compl (I.p a) (fun o => o ∈ keep a)
    rw [← hcompl]
    linarith [hdiscardMass a]
  have hden : 0 < 1 - q := by linarith [hqle]
  have hkeepPos (a : R) : 0 < keepMass a := lt_of_lt_of_le hden (hkeepLower a)
  let trimmed : ∀ a, FinProb (Ω a) := fun a =>
    FinProb.cond (I.p a) (fun o => o ∈ keep a) (hkeepPos a)
  have htrimEq (a : R) (o : Ω a) : (trimmed a).w o =
      if o ∈ keep a then (I.p a).w o / keepMass a else 0 := by
    by_cases ho : o ∈ keep a
    · simp [trimmed, FinProb.cond, keepMass, ho]
    · simp [trimmed, FinProb.cond, keepMass, ho]
  let L : ℝ := (1 - q)⁻¹
  have hLnonneg : 0 ≤ L := by dsimp [L]; positivity
  have htrimPoint (a : R) (o : Ω a) :
      (trimmed a).w o ≤ (I.p a).w o * L := by
    by_cases ho : o ∈ keep a
    · rw [htrimEq, if_pos ho, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ ((I.p a).nonneg o)
      simpa [L] using one_div_le_one_div_of_le hden (hkeepLower a)
    · rw [htrimEq, if_neg ho]
      exact mul_nonneg ((I.p a).nonneg o) hLnonneg
  have hcountq (m : ℕ) (hm : (m : ℝ) ≤ nR ^ B) :
      (m : ℝ) * q ≤ 1 / 4 := by
    calc
      (m : ℝ) * q ≤ nR ^ B * q := mul_le_mul_of_nonneg_right hm hq0
      _ = x := by
        dsimp [q, x]
        calc
          nR ^ B * nR ^ (B - P / 2) = nR ^ (B + (B - P / 2)) :=
            (Real.rpow_add hnpos _ _).symm
          _ = nR ^ (2 * B - P / 2) := by congr 1 <;> ring
      _ ≤ 1 / 4 := hxle
  have hfactorBound (m : ℕ) (hm : (m : ℝ) ≤ nR ^ B) : L ^ m ≤ 4 / 3 := by
    have hmq := hcountq m hm
    calc
      L ^ m ≤ 1 + (4 / 3 : ℝ) * (m : ℝ) * q := by
        dsimp [L]
        exact inv_one_sub_pow_le hq0 hqle hmq
      _ ≤ 4 / 3 := by nlinarith [hmq]
  have hBpow : 1 ≤ nR ^ B := Real.one_le_rpow (by linarith [hnR]) hB
  have hLle : L ≤ 4 / 3 := by
    simpa [L] using hfactorBound 1 (by norm_num; exact hBpow)
  have hLpos : 0 < L := by dsimp [L]; positivity
  have htrimLabel (a : R) (y : Fin g) :
      labMarg (trimmed a) (I.lab a) y ≤ L * labMarg (I.p a) (I.lab a) y := by
    classical
    unfold labMarg
    calc
      (∑ o, if I.lab a o = y then (trimmed a).w o else 0) ≤
          ∑ o, if I.lab a o = y then (I.p a).w o * L else 0 := by
        apply Finset.sum_le_sum
        intro o ho
        by_cases hy : I.lab a o = y
        · simp [hy]
          exact htrimPoint a o
        · simp [hy]
      _ = L * (∑ o, if I.lab a o = y then (I.p a).w o else 0) := by
        calc
          (∑ o, if I.lab a o = y then (I.p a).w o * L else 0) =
              ∑ o, L * (if I.lab a o = y then (I.p a).w o else 0) := by
            apply Finset.sum_congr rfl
            intro o ho
            by_cases hy : I.lab a o = y <;> simp [hy, mul_comm]
          _ = L * (∑ o, if I.lab a o = y then (I.p a).w o else 0) := by
            rw [← Finset.mul_sum]
  have htrimAtom (a : R) (y : Fin g) :
      labMarg (trimmed a) (I.lab a) y ≤ 2 * nR ^ (-A) := by
    calc
      labMarg (trimmed a) (I.lab a) y ≤ L * labMarg (I.p a) (I.lab a) y :=
        htrimLabel a y
      _ ≤ L * nR ^ (-A) := mul_le_mul_of_nonneg_left (hatom a y) hLnonneg
      _ ≤ 2 * nR ^ (-A) := by nlinarith [hLle, Real.rpow_nonneg (le_of_lt hnpos) (-A)]
  have htrimColumn (y : Fin g) :
      (∑ a, labMarg (trimmed a) (I.lab a) y) ≤ (4 / 3 : ℝ) * 1e-8 := by
    calc
      (∑ a, labMarg (trimmed a) (I.lab a) y) ≤
          ∑ a, L * labMarg (I.p a) (I.lab a) y :=
        Finset.sum_le_sum fun a ha => htrimLabel a y
      _ = L * ∑ a, labMarg (I.p a) (I.lab a) y := by rw [Finset.mul_sum]
      _ ≤ L * 1e-8 := mul_le_mul_of_nonneg_left (hload y) hLnonneg
      _ ≤ (4 / 3 : ℝ) * 1e-8 :=
        mul_le_mul_of_nonneg_right hLle (by norm_num)
  have htrimColumnsTotal :
      (∑ y : Fin g, ∑ a, labMarg (trimmed a) (I.lab a) y) =
        (Fintype.card R : ℝ) := by
    rw [Finset.sum_comm]
    calc
      (∑ a, ∑ y : Fin g, labMarg (trimmed a) (I.lab a) y) =
          ∑ a, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact labMarg_sum_one (trimmed a) (I.lab a)
      _ = (Fintype.card R : ℝ) := by simp
  have hrowWeight : ∀ a o, (trimmed a).w o ≤ L * (I.p a).w o := by
    intro a o
    calc
      (trimmed a).w o ≤ (I.p a).w o * L := htrimPoint a o
      _ = L * (I.p a).w o := by ring
  have hfactorGap : 4 / 3 ≤ nR ^ (2 * P / 3) := by
    have hexp : 1 ≤ 2 * P / 3 := by linarith [hP4]
    calc
      (4 / 3 : ℝ) ≤ 2 := by norm_num
      _ ≤ nR := hnR
      _ = nR ^ (1 : ℝ) := by simp
      _ ≤ nR ^ (2 * P / 3) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [hnR]) hexp
  have hfactorGapPin : 4 / 3 ≤ nR ^ (P / 6) := by
    have hexp : 1 / 2 ≤ P / 6 := by linarith [hP4]
    have hroot : (4 / 3 : ℝ) ≤ Real.sqrt nR := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [hnR]
    calc
      (4 / 3 : ℝ) ≤ Real.sqrt nR := hroot
      _ = nR ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      _ ≤ nR ^ (P / 6) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [hnR]) hexp
  have hfinalFailure : (4 / 3 : ℝ) * nR ^ (-P) ≤ nR ^ (-P / 3) := by
    calc
      (4 / 3 : ℝ) * nR ^ (-P) ≤ nR ^ (2 * P / 3) * nR ^ (-P) :=
        mul_le_mul_of_nonneg_right hfactorGap (Real.rpow_nonneg (le_of_lt hnpos) _)
      _ = nR ^ (-P / 3) := by
        calc
          nR ^ (2 * P / 3) * nR ^ (-P) = nR ^ ((2 * P / 3) + (-P)) :=
            (Real.rpow_add hnpos _ _).symm
          _ = nR ^ (-P / 3) := by congr 1 <;> ring
  have hfinalPin : (4 / 3 : ℝ) * eps ≤ nR ^ (-P / 3) := by
    calc
      (4 / 3 : ℝ) * eps ≤ nR ^ (P / 6) * eps :=
        mul_le_mul_of_nonneg_right hfactorGapPin hepspos.le
      _ = nR ^ (-P / 3) := by
        dsimp [eps]
        calc
          nR ^ (P / 6) * nR ^ (-P / 2) = nR ^ ((P / 6) + (-P / 2)) :=
            (Real.rpow_add hnpos _ _).symm
          _ = nR ^ (-P / 3) := by congr 1 <;> ring
  have htrimFailure (k : K) :
      (FinProb.pi trimmed).pr (I.failure k) ≤ nR ^ (-P / 3) := by
    have hcompare := pi_pr_depends_le I.p trimmed (I.scope k) (I.failure k)
      (hdepends k) L hLnonneg (by
        intro a ha o
        exact hrowWeight a o)
    have hfac := hfactorBound (I.scope k).card (hscope k)
    have hnonneg := finProb_pr_nonneg I.productLaw (I.failure k)
    calc
      (FinProb.pi trimmed).pr (I.failure k) ≤
          L ^ (I.scope k).card * I.productLaw.pr (I.failure k) := by
        simpa [SamplingInstance.productLaw] using hcompare
      _ ≤ (4 / 3 : ℝ) * nR ^ (-P) :=
        mul_le_mul hfac (hfailure k) hnonneg (by positivity)
      _ ≤ nR ^ (-P / 3) := hfinalFailure
  have htrimPinned (k : K) (a : R) (ha : a ∈ I.scope k) (o : Ω a)
      (ho : o ∈ keep a) :
      pinnedFailureProb trimmed I.failure k a o ≤ nR ^ (-P / 3) := by
    let G : (∀ b, Ω b) → Prop := fun ω => I.failure k ω ∧ ω a = o
    let jointT : ℝ := (FinProb.pi trimmed).pr G
    let jointP : ℝ := I.productLaw.pr G
    have hGdepends : FinProb.DependsOn G (I.scope k) := by
      intro ω ω' hagree
      change (I.failure k ω ∧ ω a = o) = (I.failure k ω' ∧ ω' a = o)
      rw [hdepends k ω ω' hagree, hagree a ha]
    have hjointCompare : jointT ≤ L ^ (I.scope k).card * jointP := by
      have hcomp := pi_pr_depends_le I.p trimmed (I.scope k) G hGdepends L hLnonneg
        (by
          intro b hb z
          exact hrowWeight b z)
      simpa [jointT, jointP, SamplingInstance.productLaw, G] using hcomp
    have hkeepGood := (Finset.mem_filter.mp ho).2
    have hkIncident : k ∈ incident a := by simp [incident, ha]
    have hpinOrig : jointP / (I.p a).w o ≤ eps := by
      simpa [jointP, pinnedFailureProb, SamplingInstance.productLaw, G] using
        (hkeepGood k hkIncident)
    by_cases hpzero : (I.p a).w o = 0
    · have htrimZero : (trimmed a).w o = 0 := by
        rw [htrimEq, if_pos ho, hpzero]
        simp
      have hcoord := pi_pr_coordinate trimmed a o
      have hjoint_le := finProb_pr_mono (FinProb.pi trimmed)
        (A := G) (B := fun ω => ω a = o) (by intro ω h; exact h.2)
      rw [hcoord] at hjoint_le
      have hjointZero : jointT = 0 := by
        apply le_antisymm
        · simpa [jointT, htrimZero] using hjoint_le
        · exact finProb_pr_nonneg (FinProb.pi trimmed) G
      have hpinZero : pinnedFailureProb trimmed I.failure k a o = 0 := by
        simp [pinnedFailureProb, SamplingInstance.productLaw, jointT, G, hjointZero, htrimZero]
      rw [hpinZero]
      positivity
    · have hpPos : 0 < (I.p a).w o := lt_of_le_of_ne ((I.p a).nonneg o) (Ne.symm hpzero)
      have hmass_le : keepMass a ≤ 1 := by
        rw [← finProb_pr_compl (I.p a) (fun z => z ∈ keep a)]
        exact le_add_of_nonneg_right
          (finProb_pr_nonneg (I.p a) (fun z => z ∉ keep a))
      have htrimLower : (I.p a).w o ≤ (trimmed a).w o := by
        rw [htrimEq, if_pos ho]
        apply (le_div_iff₀ (hkeepPos a)).2
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hmass_le ((I.p a).nonneg o)
      have hinv : ((trimmed a).w o)⁻¹ ≤ ((I.p a).w o)⁻¹ :=
        by simpa only [one_div] using one_div_le_one_div_of_le hpPos htrimLower
      have hratio : jointT / (trimmed a).w o ≤
          L ^ (I.scope k).card * (jointP / (I.p a).w o) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        calc
          jointT * ((trimmed a).w o)⁻¹ ≤
              (L ^ (I.scope k).card * jointP) * ((trimmed a).w o)⁻¹ :=
            mul_le_mul_of_nonneg_right hjointCompare
              (inv_nonneg.mpr ((trimmed a).nonneg o))
          _ ≤ (L ^ (I.scope k).card * jointP) * ((I.p a).w o)⁻¹ :=
            mul_le_mul_of_nonneg_left hinv
              (mul_nonneg (pow_nonneg hLnonneg _) (finProb_pr_nonneg I.productLaw G))
          _ = L ^ (I.scope k).card * (jointP * ((I.p a).w o)⁻¹) := by ring
      change jointT / (trimmed a).w o ≤ nR ^ (-P / 3)
      calc
        jointT / (trimmed a).w o ≤
            L ^ (I.scope k).card * (jointP / (I.p a).w o) := hratio
        _ ≤ L ^ (I.scope k).card * eps :=
          mul_le_mul_of_nonneg_left hpinOrig (pow_nonneg hLnonneg _)
        _ ≤ (4 / 3 : ℝ) * eps := by
          exact mul_le_mul_of_nonneg_right (hfactorBound (I.scope k).card (hscope k))
            hepspos.le
        _ ≤ nR ^ (-P / 3) := hfinalPin
  have hOrigColumnsTotal :
      (∑ y : Fin g, ∑ a, labMarg (I.p a) (I.lab a) y) =
        (Fintype.card R : ℝ) := by
    rw [Finset.sum_comm]
    calc
      (∑ a, ∑ y : Fin g, labMarg (I.p a) (I.lab a) y) =
          ∑ a, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact labMarg_sum_one (I.p a) (I.lab a)
      _ = (Fintype.card R : ℝ) := by simp
  have hcardRbound : (Fintype.card R : ℝ) ≤ (g : ℝ) * 1e-8 := by
    calc
      (Fintype.card R : ℝ) = ∑ y : Fin g, ∑ a, labMarg (I.p a) (I.lab a) y :=
        hOrigColumnsTotal.symm
      _ ≤ ∑ y : Fin g, (1e-8 : ℝ) :=
        Finset.sum_le_sum fun y hy => hload y
      _ = (g : ℝ) * 1e-8 := by simp
  have hcardRZero (hg : g = 0) : Fintype.card R = 0 := by
    have hreal : (Fintype.card R : ℝ) = 0 := by
      apply le_antisymm
      · simpa [hg] using hcardRbound
      · positivity
    exact_mod_cast hreal
  let targetRate : ℝ := 1e-6
  let N : ℕ := Nat.ceil (targetRate * (g : ℝ))
  let dummyRows : ℕ := N - Fintype.card R
  have hceilLow : targetRate * (g : ℝ) ≤ (N : ℝ) := by
    dsimp [N]
    exact Nat.le_ceil _
  have hcardNreal : (Fintype.card R : ℝ) ≤ (N : ℝ) := by
    calc
      (Fintype.card R : ℝ) ≤ (g : ℝ) * 1e-8 := hcardRbound
      _ ≤ targetRate * (g : ℝ) := by
        dsimp [targetRate]
        nlinarith [mul_nonneg (Nat.cast_nonneg g) (by norm_num : (0 : ℝ) ≤ 1e-8)]
      _ ≤ (N : ℝ) := hceilLow
  have hcardN : Fintype.card R ≤ N := by exact_mod_cast hcardNreal
  have hNzero (hg : g = 0) : N = 0 := by simp [N, targetRate, hg]
  have hDummyZero (hg : g = 0) : dummyRows = 0 := by
    simp [dummyRows, hNzero hg, hcardRZero hg]
  let theta : ℝ := if g = 0 then targetRate else (N : ℝ) / (g : ℝ)
  have hthetaLower : targetRate ≤ theta := by
    by_cases hg : g = 0
    · simp [theta, hg]
    · have hgpos : 0 < (g : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hg
      simpa [theta, hg] using (le_div_iff₀ hgpos).2 hceilLow
  have hthetaUpper : theta ≤ targetRate + 1 / (g : ℝ) := by
    by_cases hg : g = 0
    · simp [theta, targetRate, hg]
    · have hgpos : 0 < (g : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hg
      have hceilUp : (N : ℝ) < targetRate * (g : ℝ) + 1 := by
        dsimp [N]
        exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (Nat.cast_nonneg g))
      have hdiv : (N : ℝ) / (g : ℝ) ≤ targetRate + 1 / (g : ℝ) := by
        calc
          (N : ℝ) / (g : ℝ) ≤ (targetRate * (g : ℝ) + 1) / (g : ℝ) :=
            div_le_div_of_nonneg_right hceilUp.le hgpos.le
          _ = targetRate + 1 / (g : ℝ) := by
            field_simp [ne_of_gt hgpos]
      simpa [theta, hg] using hdiv
  have hNRow : (Fintype.card R + dummyRows : ℝ) = (N : ℝ) := by
    have hnat : Fintype.card R + (N - Fintype.card R) = N := by omega
    dsimp [dummyRows]
    exact_mod_cast hnat
  have hthetaCard : theta * (g : ℝ) = (Fintype.card R + dummyRows : ℝ) := by
    by_cases hg : g = 0
    · simp [theta, hg, hcardRZero hg, hDummyZero hg]
    · have hgpos : (g : ℝ) ≠ 0 := by exact_mod_cast hg
      have hdiv : (N : ℝ) / (g : ℝ) * (g : ℝ) =
          (Fintype.card R + dummyRows : ℝ) := by
        calc
          (N : ℝ) / (g : ℝ) * (g : ℝ) = (N : ℝ) := div_mul_cancel₀ _ hgpos
          _ = (Fintype.card R + dummyRows : ℝ) := hNRow.symm
      simpa [theta, hg] using hdiv
  have hNge2cardReal : 2 * (Fintype.card R : ℝ) ≤ (N : ℝ) := by
    calc
      2 * (Fintype.card R : ℝ) ≤ 2 * ((g : ℝ) * 1e-8) :=
        mul_le_mul_of_nonneg_left hcardRbound (by norm_num)
      _ ≤ targetRate * (g : ℝ) := by
        dsimp [targetRate]
        nlinarith [mul_nonneg (Nat.cast_nonneg g) (by norm_num : (0 : ℝ) ≤ 1e-8)]
      _ ≤ (N : ℝ) := hceilLow
  have hNge2card : 2 * Fintype.card R ≤ N := by exact_mod_cast hNge2cardReal
  have hcardLeDummy : Fintype.card R ≤ dummyRows := by
    dsimp [dummyRows]
    omega
  have hDummyPos (hg : g ≠ 0) : 0 < (dummyRows : ℝ) := by
    have hgpos : 0 < (g : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hg
    have hdiff : (targetRate * (g : ℝ) - (g : ℝ) * 1e-8) ≤
        (N : ℝ) - (Fintype.card R : ℝ) := by
      calc
        targetRate * (g : ℝ) - (g : ℝ) * 1e-8 ≤
            targetRate * (g : ℝ) - (Fintype.card R : ℝ) := by
          calc
            targetRate * (g : ℝ) - (g : ℝ) * 1e-8 =
                targetRate * (g : ℝ) + -((g : ℝ) * 1e-8) := by ring
            _ ≤ targetRate * (g : ℝ) + -((Fintype.card R : ℝ)) := by
              have hneg := add_le_add_left (neg_le_neg hcardRbound) (targetRate * (g : ℝ))
              simpa [add_comm] using hneg
            _ = targetRate * (g : ℝ) - (Fintype.card R : ℝ) := by ring
        _ ≤ (N : ℝ) - (Fintype.card R : ℝ) := sub_le_sub_right hceilLow _
    have hcast : (dummyRows : ℝ) = (N : ℝ) - (Fintype.card R : ℝ) := by
      dsimp [dummyRows]
      exact Nat.cast_sub hcardN
    rw [hcast]
    have hrateGap : 0 < targetRate - 1e-8 := by dsimp [targetRate]; norm_num
    have hgap : 0 < (targetRate - 1e-8) * (g : ℝ) := mul_pos hrateGap hgpos
    have heq : (targetRate - 1e-8) * (g : ℝ) =
        targetRate * (g : ℝ) - (g : ℝ) * 1e-8 := by ring
    rw [← heq] at hdiff
    exact lt_of_lt_of_le hgap hdiff
  let colTrim : Fin g → ℝ := fun y => ∑ a, labMarg (trimmed a) (I.lab a) y
  have hcolNonneg (y : Fin g) : 0 ≤ colTrim y := by
    dsimp [colTrim]
    exact Finset.sum_nonneg fun a ha => labMarg_nonneg (trimmed a) (I.lab a) y
  have hcolUpper (y : Fin g) : colTrim y ≤ (4 / 3 : ℝ) * 1e-8 := by
    simpa [colTrim] using htrimColumn y
  have hresNonneg (y : Fin g) : 0 ≤ theta - colTrim y := by
    have hsmall : (4 / 3 : ℝ) * 1e-8 ≤ targetRate := by norm_num
    exact sub_nonneg.mpr ((hcolUpper y).trans (hsmall.trans hthetaLower))
  have hresLeTheta (y : Fin g) : theta - colTrim y ≤ theta := by
    linarith [hcolNonneg y]
  have hcolTrimTotal : (∑ y : Fin g, colTrim y) = (Fintype.card R : ℝ) := by
    simpa [colTrim] using htrimColumnsTotal
  have hresTotal :
      (∑ y : Fin g, (theta - colTrim y)) = (dummyRows : ℝ) := by
    calc
      (∑ y : Fin g, (theta - colTrim y)) =
          (∑ y : Fin g, theta) - ∑ y : Fin g, colTrim y := by
            rw [Finset.sum_sub_distrib]
      _ = theta * (g : ℝ) - (Fintype.card R : ℝ) := by
        rw [show (∑ y : Fin g, theta) = (g : ℝ) * theta by simp, hcolTrimTotal]
        ring
      _ = (dummyRows : ℝ) := by
        calc
          theta * (g : ℝ) - (Fintype.card R : ℝ) =
              ((Fintype.card R : ℝ) + (dummyRows : ℝ)) - (Fintype.card R : ℝ) := by
            rw [hthetaCard]
          _ = (dummyRows : ℝ) := by ring
  let dummyLaw : Fin dummyRows → Fin g → ℝ :=
    fun _ y => (theta - colTrim y) / (dummyRows : ℝ)
  have hDummyNonneg : ∀ i y, 0 ≤ dummyLaw i y := by
    intro i y
    by_cases hg : g = 0
    · exact Fin.elim0 (by simpa [hg] using y)
    · exact div_nonneg (hresNonneg y) (le_of_lt (hDummyPos hg))
  have hDummyRowSum : ∀ i, ∑ y, dummyLaw i y = 1 := by
    intro i
    have hg : g ≠ 0 := by
      intro hg
      have hm0 := hDummyZero hg
      have hi := i.isLt
      omega
    have hmpos : 0 < (dummyRows : ℝ) := hDummyPos hg
    change (∑ y : Fin g, (theta - colTrim y) / (dummyRows : ℝ)) = 1
    calc
      (∑ y : Fin g, (theta - colTrim y) / (dummyRows : ℝ)) =
          (∑ y : Fin g, (theta - colTrim y)) / (dummyRows : ℝ) := by rw [Finset.sum_div]
      _ = (dummyRows : ℝ) / (dummyRows : ℝ) := by rw [hresTotal]
      _ = 1 := div_self hmpos.ne'
  have hDummyColumn (y : Fin g) :
      (∑ i : Fin dummyRows, dummyLaw i y) = theta - colTrim y := by
    have hg : g ≠ 0 := by intro hg; exact Fin.elim0 (by simpa [hg] using y)
    have hmpos : 0 < (dummyRows : ℝ) := hDummyPos hg
    change (∑ i : Fin dummyRows, (theta - colTrim y) / (dummyRows : ℝ)) =
      theta - colTrim y
    calc
      (∑ i : Fin dummyRows, (theta - colTrim y) / (dummyRows : ℝ)) =
          (dummyRows : ℝ) * ((theta - colTrim y) / (dummyRows : ℝ)) := by simp
      _ = theta - colTrim y := by field_simp [hmpos.ne']
  have hDummyAtom (i : Fin dummyRows) (y : Fin g) : dummyLaw i y ≤ 2 / (g : ℝ) := by
    have hg : g ≠ 0 := by
      intro hg
      exact Fin.elim0 (by simpa [hg] using y)
    have hmpos : 0 < (dummyRows : ℝ) := hDummyPos hg
    have hgpos : 0 < (g : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hg
    have hratio : theta / (dummyRows : ℝ) ≤ 2 / (g : ℝ) := by
      rw [div_le_div_iff₀ hmpos hgpos]
      rw [hthetaCard]
      exact_mod_cast (by omega : Fintype.card R + dummyRows ≤ 2 * dummyRows)
    calc
      dummyLaw i y = (theta - colTrim y) / (dummyRows : ℝ) := rfl
      _ ≤ theta / (dummyRows : ℝ) :=
        div_le_div_of_nonneg_right (hresLeTheta y) hmpos.le
      _ ≤ 2 / (g : ℝ) := hratio
  have hCompletedColumns (y : Fin g) :
      (∑ a, labMarg (trimmed a) (I.lab a) y) +
        (∑ i, dummyLaw i y) = theta := by
    rw [hDummyColumn]
    dsimp [colTrim]
    ring
  refine ⟨{
    keep := keep
    trimmed := trimmed
    trimmed_supported := by
      intro a o ho
      rw [htrimEq]
      simp [ho]
    trimmed_eq := htrimEq
    discarded_mass := by
      intro a
      simpa [q, nR] using hdiscardMass a
    trimmed_atom := by
      intro a y
      simpa [nR] using htrimAtom a y
    trimmed_failure := by
      intro k
      simpa [nR] using htrimFailure k
    trimmed_pinned_failure := by
      intro k a ha o ho
      simpa [nR] using htrimPinned k a ha o ho
    dummyRows := dummyRows
    dummyLaw := dummyLaw
    dummy_nonneg := hDummyNonneg
    dummy_row_sum := hDummyRowSum
    theta := theta
    theta_lower := by simpa [targetRate] using hthetaLower
    theta_upper := by simpa [targetRate] using hthetaUpper
    completed_card := hthetaCard
    completed_columns := hCompletedColumns
    dummy_atom := hDummyAtom
  }⟩

/-- The renormalization cost of Step 1 on a query of at most `n^B` rows (TeX 03:826–827, 03:1128–1131):
`(1 - n^{B-P/2})^{-n^B} ≤ 1 + 2 n^{2B-P/2}`. -/
theorem untrim_product_bound {n g : ℕ} {R K : Type*}
    [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (I : SamplingInstance n g R K Ω) (B A P : ℝ)
    (hn : 2 ≤ n) (hB : 0 ≤ B) (hBP : 4 * B + 4 ≤ P)
    (C : TrimCertificate I B A P) (S : Finset R) (o : ∀ a, Ω a)
    (hS : (S.card : ℝ) ≤ (n : ℝ) ^ B) :
    ∏ a ∈ S, (C.trimmed a).w (o a) ≤
      (1 + 2 * (n : ℝ) ^ (2 * B - P / 2)) * ∏ a ∈ S, (I.p a).w (o a) := by
  classical
  let q : ℝ := (n : ℝ) ^ (B - P / 2)
  let x : ℝ := (n : ℝ) ^ (2 * B - P / 2)
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hsmallExp : B - P / 2 ≤ -B - 2 := by linarith [hBP]
  have htotalExp : 2 * B - P / 2 ≤ -2 := by linarith [hBP]
  have hnegB : -B - 2 ≤ -2 := by linarith [hB]
  have hpow2 : (n : ℝ) ^ (-2 : ℝ) ≤ 1 / 4 := by
    calc
      (n : ℝ) ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hn) (by norm_num)
      _ = 1 / 4 := by
        rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact Real.rpow_nonneg (le_of_lt hnpos) _
  have hq_le : q ≤ 1 / 4 := by
    dsimp [q]
    calc
      (n : ℝ) ^ (B - P / 2) ≤ (n : ℝ) ^ (-B - 2) :=
        Real.rpow_le_rpow_of_exponent_le hnR hsmallExp
      _ ≤ (n : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnR hnegB
      _ ≤ 1 / 4 := hpow2
  have hx_le : x ≤ 1 / 4 := by
    dsimp [x]
    exact (Real.rpow_le_rpow_of_exponent_le hnR htotalExp).trans hpow2
  have hcardx : (S.card : ℝ) * q ≤ x := by
    calc
      (S.card : ℝ) * q ≤ (n : ℝ) ^ B * q := by
        exact mul_le_mul_of_nonneg_right hS hq_nonneg
      _ = x := by
        dsimp [q, x]
        calc
          (n : ℝ) ^ B * (n : ℝ) ^ (B - P / 2) =
              (n : ℝ) ^ (B + (B - P / 2)) := (Real.rpow_add hnpos _ _).symm
          _ = (n : ℝ) ^ (2 * B - P / 2) := by congr 1 <;> ring
  have hcardq : (S.card : ℝ) * q ≤ 1 / 4 := hcardx.trans hx_le
  have hden : 0 < 1 - q := by linarith [hq_le]
  have hpointAll (a : R) (oa : Ω a) :
      (C.trimmed a).w oa ≤ (I.p a).w oa * (1 - q)⁻¹ := by
    rw [C.trimmed_eq]
    by_cases ho : oa ∈ C.keep a
    · rw [if_pos ho, div_eq_mul_inv]
      have hcompl := finProb_pr_compl (I.p a) (fun z => z ∈ C.keep a)
      have hkeep : 1 - q ≤ (I.p a).pr (fun z => z ∈ C.keep a) := by
        rw [← hcompl]
        have hdiscard : (I.p a).pr (fun z => z ∉ C.keep a) ≤ q := by
          simpa [q] using C.discarded_mass a
        linarith
      have hinv : ((I.p a).pr (fun z => z ∈ C.keep a))⁻¹ ≤ (1 - q)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hden hkeep
      exact mul_le_mul_of_nonneg_left hinv ((I.p a).nonneg oa)
    · rw [if_neg ho]
      exact mul_nonneg ((I.p a).nonneg oa) (inv_nonneg.mpr hden.le)
  have hprod_nonneg : 0 ≤ ∏ a ∈ S, (I.p a).w (o a) :=
    Finset.prod_nonneg fun a ha => (I.p a).nonneg (o a)
  have hprod_bound :
      ∏ a ∈ S, (C.trimmed a).w (o a) ≤
        ∏ a ∈ S, ((I.p a).w (o a) * (1 - q)⁻¹) := by
    apply Finset.prod_le_prod₀
    · intro a ha
      exact (C.trimmed a).nonneg (o a)
    · intro a ha
      exact hpointAll a (o a)
  calc
    ∏ a ∈ S, (C.trimmed a).w (o a) ≤
        ∏ a ∈ S, ((I.p a).w (o a) * (1 - q)⁻¹) := hprod_bound
    _ = (∏ a ∈ S, (I.p a).w (o a)) * (1 - q)⁻¹ ^ S.card := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ (∏ a ∈ S, (I.p a).w (o a)) * (1 + 2 * (S.card : ℝ) * q) := by
      apply mul_le_mul_of_nonneg_left _ hprod_nonneg
      calc
        (1 - q)⁻¹ ^ S.card ≤
            1 + (4 / 3 : ℝ) * (S.card : ℝ) * q :=
          inv_one_sub_pow_le hq_nonneg hq_le hcardq
        _ ≤ 1 + 2 * (S.card : ℝ) * q := by nlinarith [hcardq, hq_nonneg]
    _ ≤ (∏ a ∈ S, (I.p a).w (o a)) * (1 + 2 * x) := by
      apply mul_le_mul_of_nonneg_left _ hprod_nonneg
      nlinarith [hcardx]
    _ = (1 + 2 * (n : ℝ) ^ (2 * B - P / 2)) * ∏ a ∈ S, (I.p a).w (o a) := by
      simp [x]
      ring

end HypercubeRamsey.Clock
