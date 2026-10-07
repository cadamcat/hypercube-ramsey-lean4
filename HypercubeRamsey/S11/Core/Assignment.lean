import HypercubeRamsey.S11.Core.Experiment
import HypercubeRamsey.S11.Core.Compatibility
import HypercubeRamsey.S07.SmallGridPurity
import HypercubeRamsey.S03.ClockSampling
import HypercubeRamsey.S03.ScatteredMoments
import HypercubeRamsey.S11.Core.Assignment_q_s11_even

/-!
# Proposition 11.1: taking the assignment, and the one-shot embedding

Source: `sections/11-…tex`, lines 333–394 (P11.1d1–d3 in `research/blueprint/PART-B.md` §3.11), and the assembly
of P11.1c (11:9–394).  The local-lemma tool is Section 7's `cond_product_bound` (Lemma 3.4 on product laws), the
balanced-mixture tool is `balanced_mixture_sub` (Lemma 3.3), the clock tool is `clock_sampling` (Lemma 3.10), and
the scattered-moment tool is `scattered_moments` (Lemma 3.6).
-/

namespace HypercubeRamsey.S11.Core

open HypercubeRamsey OAI.HypercubeRamsey
open Classical
open scoped BigOperators

/-! ## Reference failure and the tag stage (11:336–368) -/

/-- P11.1d1(i) (11:336–342).  Under raw tags, tuples and odd outputs, `‖M_v‖₁ < 1/2` requires either `σ_v` of
mass less than one (probability `sigmaFail ≤ e^{-.5gkh} + h(e^{-kh} + he^{-.2gk}) = n^{-ω(1)}`, P11.1b; the
radius-two data of `v` are independent `ρ_{y₀}^{⊗k}` tuples) or, given internal data with `σ_v` of mass one, an
outer mass `Z < 1/2`: the outer labels `Y_{v^j}` lie in distinct slices, are independent of the internal data,
and have unconditional law `π = Σ p_i π_i`; `σ_v` is a probability on the compatible support `supp μ_{i(s(v))}`
with `N σ_v ≤ e^{(log 2 - g/2) h}`, so Lemma 11.3 at exponent `4P + 1` applies. -/
theorem raw_mass_failure (δ x₀ K P : ℝ) (hP : 10 ≤ P) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι),
      Fixed11 δ x₀ K n N E X Y κ M y₀ p → OuterTailAt δ x₀ K (4 * P + 1) n →
      ∀ v : EvenRole n, (rawTags M p).expect (fun t => rawFail M y₀ p t v) ≤ (n : ℝ) ^ (-(4 * P)) := by
  sorry

/-- P11.1d1(ii), first event (11:349–350).  For fixed tags the conditional raw failure probability is the same at
all even roles of a slice (inner translations by even vectors preserve the raw tuple law, the odd rows and the
outer labels); Markov's inequality on the raw bound `n^{-4P}` gives `n^{-2P}`. -/
theorem t1_prob {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ) (hP : 0 < P)
    (hraw : ∀ v : EvenRole n, (rawTags M p).expect (fun t => rawFail M y₀ p t v) ≤ (n : ℝ) ^ (-(4 * P))) :
    ∀ s, (rawTags M p).pr (fun t => T1 M y₀ p P t s) ≤ (n : ℝ) ^ (-(2 * P)) := by
  sorry

/-- P11.1d1(ii), second event (11:350–352).  Given `i(s)` with `p_{i(s)} > 0` and `x ∈ supp μ_{i(s)}`,
compatibility gives exceptional tag probability at most `η` for each of the `d` independent outer neighbouring
tags; a binomial union bound gives `(4η)^{d/2}` per label and `N (4η)^{d/2} ≤ n 2^n (4η)^{(n - h)/2} ≤ n^{-2P}`. -/
theorem t2_prob (δ x₀ K P : ℝ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι),
      Fixed11 δ x₀ K n N E X Y κ M y₀ p →
      ∀ s, (rawTags M p).pr (fun t => T2 M y₀ t s) ≤ (n : ℝ) ^ (-(2 * P)) := by
  sorry

/-- P11.1d1(ii), local-lemma input (11:353–354).  Both events at `s` read only the tags of the radius-one ball of
`s` (the odd rows integrate to one away from it); balls meet only for words within distance two (at most
`(n+1)²`); and `2n^{-2P} ≤ 4n^{-2P}(1 - 4n^{-2P})^{(n+1)²}` for large `n`. -/
theorem tag_lll (δ x₀ K P : ℝ) (hP : 10 ≤ P) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι),
      Fixed11 δ x₀ K n N E X Y κ M y₀ p →
      (∀ s, (rawTags M p).pr (fun t => T1 M y₀ p P t s) ≤ (n : ℝ) ^ (-(2 * P))) →
      (∀ s, (rawTags M p).pr (fun t => T2 M y₀ t s) ≤ (n : ℝ) ^ (-(2 * P))) →
      TagLLL11 M y₀ p P := by
  sorry

/-- P11.1d1(iii), moments (11:364–368).  For pairwise separated words, remove the at most `(n+1)³` tag events
touching each radius-one ball (`cond_product_bound`, factor `2` per word); the raw tags are independent with
`E A_s(z) = N π(z)` and `E B_s(z) = N Σ p_i α_i(z)` (each neighbouring tag integrates its degree ratio to one). -/
theorem tag_moment (δ x₀ K P : ℝ) (hP : 10 ≤ P) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι),
      Fixed11 δ x₀ K n N E X Y κ M y₀ p → S07.CondProductBound → TagLLL11 M y₀ p P →
      TagMoment11 M y₀ p P := by
  sorry

/-- P11.1d1(iii) (11:356–368).  On gated tags the comparison means have caps `A_s ≤ e^{.02n}` and
`B_s ≤ 2^h · 2^d e^{O(n^.05)} · .8^{d/2} ≤ 2^n e^{-cn}` (second gate, compatibility); Lemma 3.6 with near = outer
distance at most two (fraction `(n+1)² 2^{-d}`), comparison means `≤ K` (balance) and a union over labels give
both averages at most `8(K + 1)` except with probability `≤ 1/4`. -/
theorem typical_tags (δ x₀ K P : ℝ) (hK : 0 ≤ K) (hP : 10 ≤ P) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι),
      Fixed11 δ x₀ K n N E X Y κ M y₀ p →
      0 < (rawTags M p).pr (fun t => ∀ s, ¬ TagBad M y₀ p P t s) → TagMoment11 M y₀ p P →
      (tagLaw M y₀ p P).pr (fun t => ¬ Typical11 M y₀ p (8 * (K + 1)) t) ≤ 1 / 4 := by
  sorry

/-! ## The tuple stage, odd loads and the odd injection (11:370–378) -/

/-- P11.1d2, local-lemma input (11:370–371).  `massFailGiven` at `v` reads the tuples within full-cube distance
two (internal and outer odd neighbours and their rows); events meet only within distance four (at most
`(n+1)⁴`); by the first gate and Markov, `Pr(TupleBad v) ≤ n^{2P} rawFail ≤ n^{-P} ≤ 2n^{-P}(1 - 2n^{-P})^{(n+1)⁴}`. -/
theorem tuple_lll (δ x₀ K P : ℝ) (hP : 10 ≤ P) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι),
      Fixed11 δ x₀ K n N E X Y κ M y₀ p → GatedTags M y₀ p P t → TupleLLL11 M y₀ p P t := by
  sorry

/-- P11.1d2, moments (11:373–375).  For odd roles at pairwise distance at least three, remove the at most `(n+1)³`
tuple events touching each radius-one scope (factor `2` per role); the raw rows integrate independently, and
`E_W N p_b^W(y) = N π_{i(s(b))}(y) = A_{s(b)}(y)` (the `h` neighbouring tuples are independent
`ρ_{y₀}^{⊗k}` draws). -/
theorem odd_moment (δ x₀ K P : ℝ) (hP : 10 ≤ P) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι),
      Fixed11 δ x₀ K n N E X Y κ M y₀ p → GatedTags M y₀ p P t → S07.CondProductBound →
      TupleLLL11 M y₀ p P t → OddMoment11 M y₀ p P t := by
  sorry

/-- P11.1d2, odd loads (11:373–375).  Lemma 3.6 with near = full-cube distance at most two (fraction
`(n+1)² 2^{1-n}`, cap `e^{.02n}`), comparison means of average at most `8(K + 1)` (typical tags) and a union over
labels; the odd column sum is `2^{n-1}/N` times the normalized average, at most `θ₀` once `N ≥ C₀ 2^n`. -/
theorem odd_loads (δ x₀ K P : ℝ) (hK : 0 ≤ K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
        (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι),
        Fixed11 δ x₀ K n N E X Y κ M y₀ p → GatedTags M y₀ p P t → Typical11 M y₀ p (8 * (K + 1)) t →
        OddMoment11 M y₀ p P t →
        (tupleLaw M y₀ p P t).pr (fun W => ∃ y, (1e-8 : ℝ) < oddCol M t W y) ≤ 1 / 4 := by
  sorry

/-- P11.1d2, the odd injection (11:377–378).  Lemma 3.10 (`clock_sampling`, `B = 4`, `C_g = 2`) on the odd rows
(probability laws by the slice facts, atoms `≤ e^{.02n}/N ≤ n^{-A}`, column sums `≤ θ₀` on a successful history),
with mass failure at each even role as forbidden predicate (scope its `n` odd neighbours; each odd role in `n`
scopes; product-law probability `massFailGiven ≤ n^{-P} ≤ n^{-P₀}`); `1 + ε n ≤ 2` eventually. -/
theorem clock_rows :
    ∃ P₀ : ℝ, ∀ P ≥ P₀, ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
        (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι)
        (W : EvenRole n → Fin (kTup n) → Fin N),
        SliceFacts M y₀ → GoodPre M y₀ p P t W → ∃ J, ClockOK M y₀ p t W J := by
  sorry

/-! ## Even loads, normalization and Hall (11:380–394) -/

/-- P11.1d3, star mean (11:388–390).  `N M_v(x)` reads the radius-two data of `v` (its internal odd outputs and
their rows) and, for each outer coordinate, the output at `v^j` with its row in slice `s^j`; these are disjoint
independent blocks.  The internal block integrates to `N α_{i(s(v))}(x)` (the radius-two tuples form `ballW`,
the internal odd neighbours read `ballStar`), the outer label at `v^j` to `d_G(x; π_{i(s^j)})`; the remaining odd
rows and tuples integrate to one. -/
theorem star_mean {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι)
    (hS : SliceFacts M y₀) : StarMean11 M y₀ p t := by
  exact HypercubeRamsey.Lane_q_s11_even.star_mean_full M y₀ p t hS

/-- P11.1d3, clock comparison (11:388).  The integrand reads the odd labels on the union of the separated stars'
odd neighbourhoods (at most `n² ≤ n⁴` roles); the clock comparison bounds its law by twice the product of the
odd rows, and the other rows integrate to one. -/
theorem clock_factor {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ) (t : OuterWord n → M.ι)
    (J : (EvenRole n → Fin (kTup n) → Fin N) → FinProb (OddRole n → Fin N)) (hS : SliceFacts M y₀)
    (hJ : ∀ W, GoodPre M y₀ p P t W → ClockOK M y₀ p t W (J W)) : ClockFactor11 M y₀ p P t J := by
  classical
  have hpi : ∀ y, 0 ≤ piBar M y₀ p y := by
    intro y
    unfold piBar mixW
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (p.nonneg i) ((hS.rows i).pi_nonneg y)
  have hdeg : ∀ y, 0 ≤ deg E M.G (piBar M y₀ p) y := by
    intro y
    unfold deg
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (hpi z) (by unfold hit; split_ifs <;> norm_num)
  have hrow : ∀ f v x, 0 ≤ evenRowF M y₀ p t f v x := by
    intro f v x
    unfold evenRowF
    apply mul_nonneg
    · unfold sigmaW
      split_ifs <;> positivity
    · apply Finset.prod_nonneg
      intro j hj
      exact div_nonneg (by unfold hit; split_ifs <;> norm_num) (hdeg x)
  intro W hgood x m hm a hsep
  let scope : Finset (OddRole n) :=
    Finset.univ.image fun ij : Fin m × Fin n => oddNbr (a ij.1) ij.2
  have hscope_mem (i : Fin m) (j : Fin n) : oddNbr (a i) j ∈ scope := by
    apply Finset.mem_image.mpr
    exact ⟨(i, j), Finset.mem_univ _, rfl⟩
  have hscope_card_nat : scope.card ≤ m * n := by
    calc
      scope.card ≤ (Finset.univ : Finset (Fin m × Fin n)).card := Finset.card_image_le
      _ = m * n := by simp
  have hscope_card : (scope.card : ℝ) ≤ (n : ℝ) ^ 4 := by
    have hcast : (scope.card : ℝ) ≤ (m : ℝ) * n := by exact_mod_cast hscope_card_nat
    have hmR : (m : ℝ) ≤ n := by exact_mod_cast hm
    have hmn : (m : ℝ) * n ≤ (n : ℝ) * n :=
      mul_le_mul_of_nonneg_right hmR (by positivity)
    by_cases hn0 : n = 0
    · subst n
      have hscopeEmpty : scope = ∅ := by
        dsimp [scope]
        simp
      simp [hscopeEmpty]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
      have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have hmnPow : (m : ℝ) * n ≤ (n : ℝ) ^ 2 := by simpa [pow_two] using hmn
      have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
        calc
          (n : ℝ) ^ 2 = (n : ℝ) ^ 2 * 1 := by ring
          _ ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hn2 (sq_nonneg (n : ℝ))
          _ = (n : ℝ) ^ 4 := by ring
      exact le_trans hcast (le_trans hmnPow hpow)
  have hnonemptyLaw {Ω : Type} [Fintype Ω] (Q : FinProb Ω) : Nonempty Ω := by
    by_contra h
    haveI : IsEmpty Ω := ⟨fun ω => h ⟨ω⟩⟩
    have hzero : (∑ ω, Q.w ω) = 0 := by simp
    rw [Q.sum_eq_one] at hzero
    norm_num at hzero
  let rowLaw (b : OddRole n) : FinProb (Fin N) := {
    w := oddRowF M t W b
    nonneg := (hS.rows (t (sliceOf b.1))).row_nonneg (starOf W b)
    sum_eq_one := (hS.rows (t (sliceOf b.1))).row_sum (starOf W b)
  }
  let rawLaw : FinProb (OddRole n → Fin N) := FinProb.pi rowLaw
  let restrict : (OddRole n → Fin N) → (∀ b : {b // b ∈ scope}, Fin N) :=
    fun f b => f b.1
  let defaultF : OddRole n → Fin N := Classical.choice (hnonemptyLaw (J W))
  let extend (o : ∀ b : {b // b ∈ scope}, Fin N) : OddRole n → Fin N := fun b =>
    if hb : b ∈ scope then o ⟨b, hb⟩ else defaultF b
  let val (f : OddRole n → Fin N) : ℝ :=
    ∏ i, (N : ℝ) * evenRowF M y₀ p t f (a i) x
  let marginalVal (o : ∀ b : {b // b ∈ scope}, Fin N) : ℝ := val (extend o)
  let marginal : FinProb (∀ b : {b // b ∈ scope}, Fin N) := FinProb.map (J W) restrict
  have hval_nonneg (f : OddRole n → Fin N) : 0 ≤ val f := by
    unfold val
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg (Nat.cast_nonneg _) (hrow f (a i) x)
  have hrow_ext (f g : OddRole n → Fin N)
      (hfg : ∀ b : {b // b ∈ scope}, f b.1 = g b.1) (i : Fin m) :
      evenRowF M y₀ p t f (a i) x = evenRowF M y₀ p t g (a i) x := by
    have hin : innerOut f (a i) = innerOut g (a i) := by
      funext j
      exact hfg ⟨oddNbr (a i) j.1, hscope_mem i j.1⟩
    unfold evenRowF
    rw [hin]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [hfg ⟨oddNbr (a i) j.1, hscope_mem i j.1⟩]
  have hval_ext (f g : OddRole n → Fin N)
      (hfg : ∀ b : {b // b ∈ scope}, f b.1 = g b.1) : val f = val g := by
    unfold val
    apply Finset.prod_congr rfl
    intro i hi
    rw [hrow_ext f g hfg i]
  have hext_restrict (f : OddRole n → Fin N) (b : {b // b ∈ scope}) :
      extend (restrict f) b.1 = f b.1 := by
    simp [extend, restrict, b.2]
  have hval_restrict (f : OddRole n → Fin N) : val f = marginalVal (restrict f) := by
    unfold marginalVal
    exact hval_ext f (extend (restrict f)) (fun b => (hext_restrict f b).symm)
  have hmapWeight (o : ∀ b : {b // b ∈ scope}, Fin N) :
      marginal.w o ≤ 2 * ∏ b ∈ scope, oddRowF M t W b (extend o b) := by
    have hweight : marginal.w o =
        (J W).pr (fun f => ∀ b ∈ scope, f b = extend o b) := by
      unfold marginal FinProb.map FinProb.pr
      apply Finset.sum_congr rfl
      intro f hf
      have hEqEvent : restrict f = o ↔ ∀ b ∈ scope, f b = extend o b := by
        constructor
        · intro heq b hb
          have hh := congrFun heq ⟨b, hb⟩
          simpa [restrict, extend, hb] using hh
        · intro hev
          funext b
          simpa [restrict, extend, b.2] using hev b.1 b.2
      simp [hEqEvent]
    rw [hweight]
    have hclock := (hJ W hgood).2 scope (extend o) hscope_card
    exact hclock
  have hprodAttach (o : ∀ b : {b // b ∈ scope}, Fin N) :
      (∏ b ∈ scope, oddRowF M t W b (extend o b)) =
        ∏ b : {b // b ∈ scope}, oddRowF M t W b.1 (o b) := by
    calc
      (∏ b ∈ scope, oddRowF M t W b (extend o b)) =
          ∏ b ∈ scope.attach, oddRowF M t W b.1 (extend o b.1) := by
        symm
        exact Finset.prod_attach scope (fun b => oddRowF M t W b (extend o b))
      _ = ∏ b : {b // b ∈ scope}, oddRowF M t W b.1 (o b) := by
        rw [Finset.univ_eq_attach scope]
        apply Finset.prod_congr rfl
        intro b hb
        simp [extend, b.2]
  have hmarginal :
      marginal.expect marginalVal ≤
        2 * (FinProb.pi (fun b : {b // b ∈ scope} => rowLaw b.1)).expect marginalVal := by
    unfold FinProb.expect
    calc
      ∑ o, marginal.w o * marginalVal o ≤
          ∑ o, (2 * ∏ b : {b // b ∈ scope}, oddRowF M t W b.1 (o b)) * marginalVal o := by
            apply Finset.sum_le_sum
            intro o ho
            exact mul_le_mul_of_nonneg_right (by simpa [hprodAttach] using hmapWeight o)
              (by
                unfold marginalVal
                exact hval_nonneg (extend o))
      _ = 2 * (FinProb.pi (fun b : {b // b ∈ scope} => rowLaw b.1)).expect marginalVal := by
            simp only [FinProb.expect, FinProb.pi]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro o ho
            ring
  have hMarginalPi := FinProb.pi_marginal_expect rowLaw scope marginalVal
  have hJexpect : (J W).expect val = marginal.expect marginalVal := by
    calc
      (J W).expect val = (J W).expect (fun f => marginalVal (restrict f)) := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro f hf
        rw [hval_restrict f]
      _ = marginal.expect marginalVal := by
        symm
        exact FinProb.map_expect (J W) restrict marginalVal
  have hrawExpect : (FinProb.pi rowLaw).expect val =
      ∑ f, oddProdW M t W f * val f := by
    simp [FinProb.expect, FinProb.pi, oddProdW, val, rowLaw]
  calc
    ∑ f, (J W).w f * ∏ i, (N : ℝ) * evenRowF M y₀ p t f (a i) x =
        (J W).expect val := by simp [FinProb.expect, val]
    _ = marginal.expect marginalVal := hJexpect
    _ ≤ 2 * (FinProb.pi (fun b : {b // b ∈ scope} => rowLaw b.1)).expect marginalVal := hmarginal
    _ = 2 * (FinProb.pi rowLaw).expect (fun f => marginalVal (restrict f)) := by
      rw [hMarginalPi]
    _ = 2 * (FinProb.pi rowLaw).expect val := by
      apply congrArg (fun z : ℝ => 2 * z)
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro f hf
      rw [hval_restrict f]
    _ = 2 * ∑ f, oddProdW M t W f * val f := by rw [hrawExpect]

/-- P11.1d3, tuple integral (11:388–390).  Remove the at most `(n+1)⁴` tuple events touching each radius-two
scope (`cond_product_bound`, factor `2` per star); the separated scopes (distance at least five) are disjoint, so
the raw integral factors into star means. -/
theorem even_tuple_integral (δ x₀ K P : ℝ) (hP : 10 ≤ P) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι),
      Fixed11 δ x₀ K n N E X Y κ M y₀ p → GatedTags M y₀ p P t → S07.CondProductBound →
      TupleLLL11 M y₀ p P t → StarMean11 M y₀ p t → EvenTupleIntegral11 M y₀ p P t := by
  sorry

/-- P11.1d3, assembled moment (11:386–390): drop the success indicator after the clock comparison and integrate
(`2 · 2^m ≤ 4^m` for `m ≥ 1`; for `m = 0` both sides are at most one). -/
theorem even_moment {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ) (t : OuterWord n → M.ι)
    (J : (EvenRole n → Fin (kTup n) → Fin N) → FinProb (OddRole n → Fin N)) (hS : SliceFacts M y₀)
    (hcf : ClockFactor11 M y₀ p P t J) (hint : EvenTupleIntegral11 M y₀ p P t) :
    EvenMoment11 M y₀ p P t J := by
  classical
  intro x m hm a hsep
  by_cases hm0 : m = 0
  · subst m
    have hmass :
        ∑ W, (tupleLaw M y₀ p P t).w W *
          (if GoodPre M y₀ p P t W then 1 else 0) ≤ 1 := by
      calc
        _ ≤ ∑ W, (tupleLaw M y₀ p P t).w W := by
          apply Finset.sum_le_sum
          intro W hW
          by_cases hg : GoodPre M y₀ p P t W
          · simp [hg, (tupleLaw M y₀ p P t).nonneg W]
          · simpa [hg] using (tupleLaw M y₀ p P t).nonneg W
        _ = 1 := (tupleLaw M y₀ p P t).sum_eq_one
    have hJsum' (W : EvenRole n → Fin (kTup n) → Fin N) : ∑ f, (J W).w f = 1 :=
      (J W).sum_eq_one
    simpa [EvenMoment11, hJsum'] using hmass
  · have hpi : ∀ y, 0 ≤ piBar M y₀ p y := by
      intro y
      unfold piBar mixW
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (p.nonneg i) ((hS.rows i).pi_nonneg y)
    have hdeg : ∀ y, 0 ≤ deg E M.G (piBar M y₀ p) y := by
      intro y
      unfold deg
      apply Finset.sum_nonneg
      intro z hz
      exact mul_nonneg (hpi z) (by
        unfold hit
        split_ifs <;> norm_num)
    have hdegRow : ∀ i y, 0 ≤ deg E M.G (piRow M y₀ i) y := by
      intro i y
      unfold deg
      apply Finset.sum_nonneg
      intro z hz
      exact mul_nonneg ((hS.rows i).pi_nonneg z) (by
        unfold hit
        split_ifs <;> norm_num)
    have hrow : ∀ f v x, 0 ≤ evenRowF M y₀ p t f v x := by
      intro f v x
      unfold evenRowF
      apply mul_nonneg
      · unfold sigmaW
        split_ifs <;> positivity
      · apply Finset.prod_nonneg
        intro j hj
        exact div_nonneg (by
          unfold hit
          split_ifs <;> norm_num) (hdeg x)
    have hfactor : ∀ f i, 0 ≤ (N : ℝ) * evenRowF M y₀ p t f (a i) x := by
      intro f i
      exact mul_nonneg (Nat.cast_nonneg _) (hrow f (a i) x)
    have hodd : ∀ W f, 0 ≤ oddProdW M t W f := by
      intro W f
      unfold oddProdW
      apply Finset.prod_nonneg
      intro b hb
      exact (hS.rows (t (sliceOf b.1))).row_nonneg (starOf W b) (f b)
    let raw (W : EvenRole n → Fin (kTup n) → Fin N) : ℝ :=
      ∑ f, oddProdW M t W f * ∏ i, (N : ℝ) * evenRowF M y₀ p t f (a i) x
    have hraw : ∀ W, 0 ≤ raw W := by
      intro W
      dsimp [raw]
      apply Finset.sum_nonneg
      intro f hf
      exact mul_nonneg (hodd W f) (Finset.prod_nonneg fun i hi => hfactor f i)
    have hpoint : ∀ W,
        (if GoodPre M y₀ p P t W then
          ∑ f, (J W).w f * ∏ i, (N : ℝ) * evenRowF M y₀ p t f (a i) x else 0) ≤ 2 * raw W := by
      intro W
      by_cases hg : GoodPre M y₀ p P t W
      · simp only [hg, if_true]
        have hc := hcf W hg x m hm a hsep
        simpa only [FinProb.expect, raw] using hc
      · simp only [hg, if_false]
        exact mul_nonneg (by norm_num) (hraw W)
    have hsum :
        ∑ W, (tupleLaw M y₀ p P t).w W *
          (if GoodPre M y₀ p P t W then
            ∑ f, (J W).w f * ∏ i, (N : ℝ) * evenRowF M y₀ p t f (a i) x else 0) ≤
          2 * (tupleLaw M y₀ p P t).expect raw := by
      calc
        _ ≤ ∑ W, (tupleLaw M y₀ p P t).w W * (2 * raw W) := by
          apply Finset.sum_le_sum
          intro W hW
          exact mul_le_mul_of_nonneg_left (hpoint W) ((tupleLaw M y₀ p P t).nonneg W)
        _ = 2 * (tupleLaw M y₀ p P t).expect raw := by
          simp [FinProb.expect, raw, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    have htuple := hint x m hm a hsep
    have hcomp : 0 ≤ ∏ i, compB M y₀ p t (sliceOf (a i).1) x := by
      apply Finset.prod_nonneg
      intro i hi
      unfold compB
      apply mul_nonneg
      · exact mul_nonneg (Nat.cast_nonneg _) ((hS.alpha (t (sliceOf (a i).1))).nonneg x)
      · apply Finset.prod_nonneg
        intro j hj
        exact div_nonneg (hdegRow (t (flipOuter (sliceOf (a i).1) j)) x) (hdeg x)
    have hpow : 2 * (2 : ℝ) ^ m ≤ (4 : ℝ) ^ m := by
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      have hle : m + 1 ≤ 2 * m := by omega
      calc
        2 * (2 : ℝ) ^ m = (2 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
        _ ≤ (2 : ℝ) ^ (2 * m) := by
          exact pow_le_pow_right₀ (by norm_num) hle
        _ = (4 : ℝ) ^ m := by rw [pow_mul]; norm_num
    unfold EvenTupleIntegral11 at htuple
    unfold FinProb.expect at hsum
    calc
      _ = ∑ W, (tupleLaw M y₀ p P t).w W *
          (if GoodPre M y₀ p P t W then
            ∑ f, (J W).w f * ∏ i, (N : ℝ) * evenRowF M y₀ p t f (a i) x else 0) := rfl
      _ ≤ 2 * ∑ W, (tupleLaw M y₀ p P t).w W * raw W := by
        simpa [FinProb.expect, raw] using hsum
      _ ≤ 2 * ((2 : ℝ) ^ m * ∏ i, compB M y₀ p t (sliceOf (a i).1) x) := by
        exact mul_le_mul_of_nonneg_left (by simpa [FinProb.expect, raw] using htuple) (by norm_num)
      _ ≤ (4 : ℝ) ^ m * ∏ i, compB M y₀ p t (sliceOf (a i).1) x := by
        calc
          _ = (2 * (2 : ℝ) ^ m) * ∏ i, compB M y₀ p t (sliceOf (a i).1) x := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hpow hcomp

/-- P11.1d3, even loads (11:380–393).  `N M_v(x) ≤ 2^n e^{-gh/2 + O(n^.05)} ≤ 2^n e^{-.4gh}` (`σ_v ≤ 1/cutoff`,
`D_x ≥ 1/2 - 2b_*` on the compatible support); Lemma 3.6 with near = full-cube distance at most four (fraction
`(n+1)⁴ 2^{1-n}`), comparison means `B_{s(v)}(x)` of average at most `8(K + 1)` (typical tags) and a union over
labels; the column sum is `2^{n-1}/N` times the normalized average, at most `1/2` once `N ≥ C₀ 2^n`. -/
theorem even_loads (δ x₀ K P : ℝ) (hK : 0 ≤ K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
        (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι)
        (J : (EvenRole n → Fin (kTup n) → Fin N) → FinProb (OddRole n → Fin N)),
        Fixed11 δ x₀ K n N E X Y κ M y₀ p → GatedTags M y₀ p P t → Typical11 M y₀ p (8 * (K + 1)) t →
        (∀ W, GoodPre M y₀ p P t W → ClockOK M y₀ p t W (J W)) → EvenMoment11 M y₀ p P t J →
        ∑ W, (tupleLaw M y₀ p P t).w W *
            (if GoodPre M y₀ p P t W then
              (J W).pr (fun f => ∃ x, 1 / 2 < ∑ v, evenRowF M y₀ p t f v x) else 0) ≤ 1 / 4 := by
  sorry

/-- P11.1d1–d3 averaged (11:368, 375, 378, 393).  The tag law is supported on gated tags and gives gated typical
tags with probability `≥ 3/4`; at such tags the tuple law is supported on tuples without tuple events and gives a
successful history with probability `≥ 3/4`; choose clock laws at successful histories; the even column sums
exceed `1/2` with probability `≤ 1/4`, so some successful history and some outcome of its clock law have an
injective odd assignment avoiding all mass failures and even column sums at most `1/2`. -/
theorem realization {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P C : ℝ)
    (htyp : (tagLaw M y₀ p P).pr (fun t => ¬ Typical11 M y₀ p C t) ≤ 1 / 4)
    (htag : 0 < (rawTags M p).pr (fun t => ∀ s, ¬ TagBad M y₀ p P t s))
    (htup : ∀ t, GatedTags M y₀ p P t →
      0 < (rawTuples M y₀ t).pr (fun W => ∀ v, ¬ TupleBad M y₀ p P t v W))
    (hodd : ∀ t, GatedTags M y₀ p P t → Typical11 M y₀ p C t →
      (tupleLaw M y₀ p P t).pr (fun W => ∃ y, (1e-8 : ℝ) < oddCol M t W y) ≤ 1 / 4)
    (hclock : ∀ t W, GoodPre M y₀ p P t W → ∃ J, ClockOK M y₀ p t W J)
    (heven : ∀ t, GatedTags M y₀ p P t → Typical11 M y₀ p C t →
      ∀ J : (EvenRole n → Fin (kTup n) → Fin N) → FinProb (OddRole n → Fin N),
        (∀ W, GoodPre M y₀ p P t W → ClockOK M y₀ p t W (J W)) →
        ∑ W, (tupleLaw M y₀ p P t).w W *
            (if GoodPre M y₀ p P t W then
              (J W).pr (fun f => ∃ x, 1 / 2 < ∑ v, evenRowF M y₀ p t f v x) else 0) ≤ 1 / 4) :
    ∃ (t : OuterWord n → M.ι) (f : OddRole n → Fin N), Function.Injective f ∧
      (∀ v, ¬ MassFail M y₀ p t f v) ∧ ∀ x, ∑ v, evenRowF M y₀ p t f v x ≤ 1 / 2 := by
  classical
  have hcompl {Ω : Type} [Fintype Ω] (Q : FinProb Ω) (A : Ω → Prop) :
      Q.pr A + Q.pr (fun ω => ¬ A ω) = 1 := by
    have hsum : Q.pr A + Q.pr (fun ω => ¬ A ω) = ∑ ω : Ω, Q.w ω := by
      unfold FinProb.pr
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hA : A ω <;> simp [hA]
    rw [hsum, Q.sum_eq_one]
  have hpos_support {Ω : Type} [Fintype Ω] (Q : FinProb Ω) (A : Ω → Prop)
      (hA : 0 < Q.pr A) : ∃ ω, Q.w ω ≠ 0 ∧ A ω := by
    by_contra h
    have hcases : ∀ ω, Q.w ω = 0 ∨ ¬ A ω := by
      intro ω
      by_cases hw : Q.w ω = 0
      · exact Or.inl hw
      · exact Or.inr (fun hω => h ⟨ω, hw, hω⟩)
    have hz : Q.pr A = 0 := by
      change ∑ ω : Ω, (if A ω then Q.w ω else 0) = 0
      apply Finset.sum_eq_zero
      intro ω hω
      by_cases hAw : A ω
      · rcases hcases ω with hw | hnot
        · simp [hAw, hw]
        · exact (hnot hAw).elim
      · simp [hAw]
    linarith
  have hmono {Ω : Type} [Fintype Ω] (Q : FinProb Ω) (A B : Ω → Prop)
      (hAB : ∀ ω, Q.w ω ≠ 0 → A ω → B ω) : Q.pr A ≤ Q.pr B := by
    classical
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro ω hω
    by_cases hw : Q.w ω = 0
    · simp [hw]
    · by_cases hA : A ω
      · have hB := hAB ω hw hA
        simp [hA, hB]
      · by_cases hB : B ω <;> simp [hA, hB, Q.nonneg ω]
  have htypicalPos : 0 < (tagLaw M y₀ p P).pr (fun t => Typical11 M y₀ p C t) := by
    have hc := hcompl (tagLaw M y₀ p P) (fun t => Typical11 M y₀ p C t)
    have hb := htyp
    linarith
  obtain ⟨t, htw, htypical⟩ := hpos_support (tagLaw M y₀ p P)
    (fun t => Typical11 M y₀ p C t) htypicalPos
  have hclear : ∀ s, ¬ TagBad M y₀ p P t s := by
    by_contra h
    push_neg at h
    obtain ⟨s, hs⟩ := h
    have hnot : ¬ (∀ s, ¬ TagBad M y₀ p P t s) := fun hall => hall s hs
    have hz : (tagLaw M y₀ p P).w t = 0 := by
      simp [tagLaw, S07.condOr, htag, hnot, FinProb.cond]
    exact htw hz
  have hrawTag : (rawTags M p).w t ≠ 0 := by
    intro hz
    apply htw
    simp [tagLaw, S07.condOr, htag, hclear, FinProb.cond, hz]
  have htagSupport : ∀ s, p.w (t s) ≠ 0 := by
    have hprod : (∏ s : OuterWord n, p.w (t s)) ≠ 0 := by
      simpa [rawTags, FinProb.pi] using hrawTag
    intro s
    exact (Finset.prod_ne_zero_iff.mp hprod) s (Finset.mem_univ s)
  have hgate : GatedTags M y₀ p P t := ⟨htagSupport, hclear⟩
  have htuplePos := htup t hgate
  have htupleClean (W : EvenRole n → Fin (kTup n) → Fin N)
      (hW : (tupleLaw M y₀ p P t).w W ≠ 0) : ∀ v, ¬ TupleBad M y₀ p P t v W := by
    intro v
    by_contra hbad
    have hnot : ¬ (∀ u, ¬ TupleBad M y₀ p P t u W) := by
      intro hall
      exact hall v hbad
    have hrawPos : 0 < (rawTuples M y₀ t).pr
        (fun W => ∀ a : CubeVertex n, ∀ b : IsEvenRole a,
          ¬ TupleBad M y₀ p P t ⟨a, b⟩ W) := by
      simpa only [Subtype.forall] using htuplePos
    have hnot' : ¬ (∀ a : CubeVertex n, ∀ b : IsEvenRole a,
        ¬ TupleBad M y₀ p P t ⟨a, b⟩ W) := by
      simpa only [Subtype.forall] using hnot
    apply hW
    change (S07.condOr (rawTuples M y₀ t)
      (fun W => ∀ v : EvenRole n, ¬ TupleBad M y₀ p P t v W)).w W = 0
    simp [S07.condOr, FinProb.cond, Subtype.forall, hrawPos, hnot']
  let oddBad (W : EvenRole n → Fin (kTup n) → Fin N) : Prop :=
    ∃ y, (1e-8 : ℝ) < oddCol M t W y
  have hnotGoodSub : ∀ W, (tupleLaw M y₀ p P t).w W ≠ 0 →
      ¬ GoodPre M y₀ p P t W → oddBad W := by
    intro W hW hnot
    have hclean := htupleClean W hW
    by_contra hbad
    apply hnot
    refine ⟨hclean, ?_⟩
    intro y
    by_contra hle
    exact hbad ⟨y, lt_of_not_ge hle⟩
  have hnotPreProb :
      (tupleLaw M y₀ p P t).pr (fun W => ¬ GoodPre M y₀ p P t W) ≤
        (tupleLaw M y₀ p P t).pr oddBad :=
    hmono (tupleLaw M y₀ p P t) (fun W => ¬ GoodPre M y₀ p P t W) oddBad hnotGoodSub
  have hgoodPreProb : 3 / 4 ≤ (tupleLaw M y₀ p P t).pr (fun W => GoodPre M y₀ p P t W) := by
    have hc := hcompl (tupleLaw M y₀ p P t) (fun W => GoodPre M y₀ p P t W)
    have hb : (tupleLaw M y₀ p P t).pr oddBad ≤ 1 / 4 := by
      simpa [oddBad] using hodd t hgate htypical
    have hb' := le_trans hnotPreProb hb
    linarith
  have hgoodPrePos : 0 < (tupleLaw M y₀ p P t).pr (fun W => GoodPre M y₀ p P t W) := by
    linarith
  obtain ⟨W₀, hW₀, hgood₀⟩ := hpos_support (tupleLaw M y₀ p P t)
    (fun W => GoodPre M y₀ p P t W) hgoodPrePos
  obtain ⟨J₀, hJ₀⟩ := hclock t W₀ hgood₀
  let J' : (EvenRole n → Fin (kTup n) → Fin N) → FinProb (OddRole n → Fin N) := fun W =>
    if h : GoodPre M y₀ p P t W then Classical.choose (hclock t W h) else J₀
  have hJ' : ∀ W, GoodPre M y₀ p P t W → ClockOK M y₀ p t W (J' W) := by
    intro W hW
    simp [J', hW, Classical.choose_spec (hclock t W hW)]
  have hevenBad := heven t hgate htypical J' hJ'
  let evenBad (f : OddRole n → Fin N) : Prop := ∃ x, 1 / 2 < ∑ v, evenRowF M y₀ p t f v x
  let badMass : ℝ := ∑ W, (tupleLaw M y₀ p P t).w W *
    (if GoodPre M y₀ p P t W then (J' W).pr evenBad else 0)
  let goodMass : ℝ := ∑ W, (tupleLaw M y₀ p P t).w W *
    (if GoodPre M y₀ p P t W then (J' W).pr (fun f => ¬ evenBad f) else 0)
  have hmassSplit : goodMass + badMass =
      (tupleLaw M y₀ p P t).pr (fun W => GoodPre M y₀ p P t W) := by
    unfold goodMass badMass
    rw [← Finset.sum_add_distrib]
    calc
      ∑ W, ((tupleLaw M y₀ p P t).w W *
          (if GoodPre M y₀ p P t W then (J' W).pr (fun f => ¬ evenBad f) else 0) +
            (tupleLaw M y₀ p P t).w W *
          (if GoodPre M y₀ p P t W then (J' W).pr evenBad else 0)) =
        ∑ W, (if GoodPre M y₀ p P t W then (tupleLaw M y₀ p P t).w W else 0) := by
          apply Finset.sum_congr rfl
          intro W hW
          by_cases hg : GoodPre M y₀ p P t W
          · have hc := hcompl (J' W) evenBad
            have hc' : (J' W).pr (fun f => ¬ evenBad f) + (J' W).pr evenBad = 1 := by
              linarith
            simp only [hg, if_true]
            calc
              (tupleLaw M y₀ p P t).w W * (J' W).pr (fun f => ¬ evenBad f) +
                  (tupleLaw M y₀ p P t).w W * (J' W).pr evenBad =
                (tupleLaw M y₀ p P t).w W *
                  ((J' W).pr (fun f => ¬ evenBad f) + (J' W).pr evenBad) := by ring
              _ = (tupleLaw M y₀ p P t).w W := by rw [hc']; ring
          · simp [hg]
      _ = (tupleLaw M y₀ p P t).pr (fun W => GoodPre M y₀ p P t W) := by
        unfold FinProb.pr
        rfl
  have hbadMass : badMass ≤ 1 / 4 := by
    simpa [badMass, evenBad] using hevenBad
  have hgoodMassPos : 0 < goodMass := by
    have hp := hgoodPreProb
    linarith [hmassSplit, hbadMass]
  let joint := FinProb.bind (tupleLaw M y₀ p P t) J'
  have hjointFormula : joint.pr (fun wf => GoodPre M y₀ p P t wf.1 ∧ ¬ evenBad wf.2) = goodMass := by
    unfold joint goodMass FinProb.pr FinProb.bind
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro W hW
    by_cases hg : GoodPre M y₀ p P t W
    · simp [hg, FinProb.pr, Finset.mul_sum]
    · simp [hg, FinProb.pr]
  obtain ⟨⟨W, f⟩, hwf, hsuccess⟩ := hpos_support joint
      (fun wf => GoodPre M y₀ p P t wf.1 ∧ ¬ evenBad wf.2)
      (by rw [hjointFormula]; exact hgoodMassPos)
  have hW : (tupleLaw M y₀ p P t).w W ≠ 0 := by
    have hmul : (tupleLaw M y₀ p P t).w W * (J' W).w f ≠ 0 := by
      simpa [joint, FinProb.bind] using hwf
    exact left_ne_zero_of_mul hmul
  have hf : (J' W).w f ≠ 0 := by
    have hmul : (tupleLaw M y₀ p P t).w W * (J' W).w f ≠ 0 := by
      simpa [joint, FinProb.bind] using hwf
    exact right_ne_zero_of_mul hmul
  have hclockW := hJ' W hsuccess.1
  have hgoodf := hclockW.1 f hf
  have hcols : ∀ x, ∑ v, evenRowF M y₀ p t f v x ≤ 1 / 2 := by
    intro x
    exact le_of_not_gt (fun hx => hsuccess.2 ⟨x, hx⟩)
  exact ⟨t, f, hgoodf.1, hgoodf.2, hcols⟩

/-- P11.1d3, normalization and Hall (11:393–394).  Every row has mass at least `1/2`; the normalized rows are
probability laws supported on common neighbours of the odd labels (`σ_v(x) ≠ 0` puts `x` in the common-neighbour
set of the internal odd neighbours, the outer factors are hits of the outer neighbours; every cube neighbour of
`v` is an inner or an outer flip), with column sums at most `2 · 1/2`; F-HallEmbed (`cubeAt_of_rows`). -/
theorem hall_of_realization {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι)
    (f : OddRole n → Fin N) (hS : SliceFacts M y₀) (hinj : Function.Injective f)
    (hmf : ∀ v, ¬ MassFail M y₀ p t f v) (hcol : ∀ x, ∑ v, evenRowF M y₀ p t f v x ≤ 1 / 2) :
    CubeAt n N E := by
  classical
  have hpi : ∀ y, 0 ≤ piBar M y₀ p y := by
    intro y
    unfold piBar mixW
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (p.nonneg i) ((hS.rows i).pi_nonneg y)
  have hdeg : ∀ y, 0 ≤ deg E M.G (piBar M y₀ p) y := by
    intro y
    unfold deg
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (hpi z) (by unfold hit; split_ifs <;> norm_num)
  have hrow : ∀ a x, 0 ≤ evenRowF M y₀ p t f a x := by
    intro a x
    unfold evenRowF
    apply mul_nonneg
    · unfold sigmaW
      split_ifs <;> positivity
    · apply Finset.prod_nonneg
      intro j hj
      exact div_nonneg (by unfold hit; split_ifs <;> norm_num) (hdeg x)
  let mass : EvenRole n → ℝ := fun a => ∑ x, evenRowF M y₀ p t f a x
  let row : EvenRole n → Fin N → ℝ := fun a x => evenRowF M y₀ p t f a x / mass a
  have hmass_lower (a : EvenRole n) : 1 / 2 ≤ mass a := by
    have hn := hmf a
    change ¬ (∑ x, evenRowF M y₀ p t f a x < 1 / 2) at hn
    exact le_of_not_gt (by simpa [mass] using hn)
  have hmass_pos (a : EvenRole n) : 0 < mass a := by
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    exact lt_of_lt_of_le hhalf (hmass_lower a)
  have hrow_nonneg : ∀ a x, 0 ≤ row a x := by
    intro a x
    exact div_nonneg (hrow a x) (hmass_pos a).le
  have hrow_sum (a : EvenRole n) : ∑ x, row a x = 1 := by
    calc
      ∑ x, row a x = (∑ x, evenRowF M y₀ p t f a x) / mass a := by
        simp [row, Finset.sum_div]
      _ = mass a / mass a := rfl
      _ = 1 := div_self (ne_of_gt (hmass_pos a))
  have hrow_col : ∀ x, ∑ a, row a x ≤ 1 := by
    intro x
    have hpoint (a : EvenRole n) : row a x ≤ 2 * evenRowF M y₀ p t f a x := by
      apply (div_le_iff₀ (hmass_pos a)).2
      have hm := mul_le_mul_of_nonneg_left (hmass_lower a) (hrow a x)
      dsimp [row, mass] at hm ⊢
      nlinarith
    calc
      ∑ a, row a x ≤ ∑ a, 2 * evenRowF M y₀ p t f a x :=
        Finset.sum_le_sum fun a ha => hpoint a
      _ = 2 * ∑ a, evenRowF M y₀ p t f a x := by rw [← Finset.mul_sum]
      _ ≤ 1 := by
        have hc := mul_le_mul_of_nonneg_left (hcol x) (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith
  have hsupp : ∀ a x, row a x ≠ 0 → ∀ b : OddRole n,
      (cube n).Adj a.1 b.1 → Hits E M.G x (f b) := by
    intro a x hpx b hab
    have hmassNe : mass a ≠ 0 := (hmass_pos a).ne'
    have hrowNe : evenRowF M y₀ p t f a x ≠ 0 := by
      intro hz
      apply hpx
      simp [row, hz]
    have hfactorNe :
        (sigmaW E M.G (gS n) (M.μ (t (sliceOf a.1))) (innerOut f a) x) ≠ 0 ∧
          (∏ j : OuterCoord n,
            hit E M.G x (f (oddNbr a j.1)) / deg E M.G (piBar M y₀ p) x) ≠ 0 := by
      simpa [evenRowF] using (mul_ne_zero_iff.mp hrowNe)
    have hcommon : x ∈ commonSet E M.G (M.μ (t (sliceOf a.1))) (innerOut f a) := by
      have hcond : x ∈ commonSet E M.G (M.μ (t (sliceOf a.1))) (innerOut f a) ∧
          (N : ℝ) * Real.exp (-((Real.log 2 - gS n / 2) * Fintype.card (InnerCoord n))) ≤
            ((commonSet E M.G (M.μ (t (sliceOf a.1))) (innerOut f a)).card : ℝ) := by
        by_cases hc : x ∈ commonSet E M.G (M.μ (t (sliceOf a.1))) (innerOut f a) ∧
            (N : ℝ) * Real.exp (-((Real.log 2 - gS n / 2) * Fintype.card (InnerCoord n))) ≤
              ((commonSet E M.G (M.μ (t (sliceOf a.1))) (innerOut f a)).card : ℝ)
        · exact hc
        · simp [sigmaW, hc] at hfactorNe
      exact hcond.1
    change hammingDist a.1 b.1 = 1 at hab
    let S : Finset (Fin n) := Finset.univ.filter fun j => a.1 j ≠ b.1 j
    have hS : S.card = 1 := by simpa [S, hammingDist] using hab
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have hflip : b.1 = cubeFlip a.1 j := by
      funext k
      by_cases hkj : k = j
      · subst k
        have hdiff : a.1 j ≠ b.1 j := (Finset.mem_filter.mp hj).2
        cases ha : a.1 j <;> cases hb : b.1 j <;> simp_all [cubeFlip]
      · have heq : a.1 k = b.1 k := by
          by_contra hne
          have hk : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
          have hjk : j ≠ k := fun heq => hkj heq.symm
          have htwo : 1 < S.card := Finset.one_lt_card.mpr ⟨j, hj, k, hk, hjk⟩
          omega
        simp [cubeFlip, Function.update_of_ne hkj, heq]
    have hnbr : oddNbr a j = b := by
      apply Subtype.ext
      exact hflip.symm
    by_cases hjI : j.val < hIn n
    · let ji : InnerCoord n := ⟨j, hjI⟩
      have hhit := (Finset.mem_filter.mp hcommon).2.2 ji
      have hhit' : Hits E M.G x (f (oddNbr a j)) := by
        simpa [innerOut, ji] using hhit
      have htarget : Hits E M.G x (f b) := by
        rw [← hnbr]
        exact hhit'
      exact htarget
    · have hjO : hIn n ≤ j.val := by omega
      let jo : OuterCoord n := ⟨j, hjO⟩
      have houter :
          hit E M.G x (f (oddNbr a j)) / deg E M.G (piBar M y₀ p) x ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hfactorNe.2) jo (Finset.mem_univ jo)
      have hhit : hit E M.G x (f (oddNbr a j)) ≠ 0 := by
        intro hz
        apply houter
        simp [hz]
      have htarget : Hits E M.G x (f b) := by
        unfold hit at hhit
        split_ifs at hhit with hh
        · rw [← hnbr]
          exact hh
        · norm_num at hhit
      exact htarget
  exact cubeAt_of_rows E M.G f hinj row hrow_nonneg hrow_sum hsupp hrow_col

/-- P11.1d1–d3 assembled: at a fixed menu, slice facts, compatible balanced profile and (11.1), Lemma 11.3 at the
dimension gives the cube. -/
theorem assignment_cube (δ x₀ K : ℝ) (hK : 0 < K) :
    ∃ P : ℝ, 10 ≤ P ∧ ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
        (y₀ : M.ι → Fin N) (p : FinProb M.ι),
        Fixed11 δ x₀ K n N E X Y κ M y₀ p → OuterTailAt δ x₀ K (4 * P + 1) n → CubeAt n N E := by
  obtain ⟨P₀, hclock⟩ := clock_rows
  have hP : (10 : ℝ) ≤ max P₀ 10 := le_max_right _ _
  refine ⟨max P₀ 10, hP, ?_⟩
  obtain ⟨nC, CC, hJ⟩ := hclock (max P₀ 10) (le_max_left _ _)
  obtain ⟨n₁, hraw⟩ := raw_mass_failure δ x₀ K (max P₀ 10) hP
  obtain ⟨n₂, ht2⟩ := t2_prob δ x₀ K (max P₀ 10)
  obtain ⟨n₃, htag⟩ := tag_lll δ x₀ K (max P₀ 10) hP
  obtain ⟨n₄, hmomT⟩ := tag_moment δ x₀ K (max P₀ 10) hP
  obtain ⟨n₅, htyp⟩ := typical_tags δ x₀ K (max P₀ 10) hK.le hP
  obtain ⟨n₆, htup⟩ := tuple_lll δ x₀ K (max P₀ 10) hP
  obtain ⟨n₇, hmomO⟩ := odd_moment δ x₀ K (max P₀ 10) hP
  obtain ⟨n₈, C₈, hodd⟩ := odd_loads δ x₀ K (max P₀ 10) hK.le
  obtain ⟨n₉, hint⟩ := even_tuple_integral δ x₀ K (max P₀ 10) hP
  obtain ⟨n₁₀, C₁₀, heven⟩ := even_loads δ x₀ K (max P₀ 10) hK.le
  refine ⟨max (max (max nC n₁) (max n₂ n₃)) (max (max n₄ n₅) (max (max n₆ n₇) (max (max n₈ n₉) n₁₀))),
    max (max CC C₈) (max C₁₀ 1), ?_⟩
  intro n N hL E X Y κ M y₀ p hF htail
  have hn := hL.1
  have hLC : LargeAt nC CC n N :=
    S07.largeAt_weaken hL (by omega) (le_trans (le_max_left CC C₈) (le_max_left _ _))
  have hL8 : LargeAt n₈ C₈ n N :=
    S07.largeAt_weaken hL (by omega) (le_trans (le_max_right CC C₈) (le_max_left _ _))
  have hL10 : LargeAt n₁₀ C₁₀ n N :=
    S07.largeAt_weaken hL (by omega) (le_trans (le_max_left C₁₀ 1) (le_max_right _ _))
  have hT1 := t1_prob M y₀ p (max P₀ 10) (by linarith) (hraw n (by omega) M y₀ p hF htail)
  have hTL : TagLLL11 M y₀ p (max P₀ 10) :=
    htag n (by omega) M y₀ p hF hT1 (ht2 n (by omega) M y₀ p hF)
  have hTpos := (S07.cond_product_bound _ _ _ _ _ hTL).1
  have hTM := hmomT n (by omega) M y₀ p hF S07.cond_product_bound hTL
  have hUL : ∀ t, GatedTags M y₀ p (max P₀ 10) t → TupleLLL11 M y₀ p (max P₀ 10) t :=
    fun t ht => htup n (by omega) M y₀ p t hF ht
  obtain ⟨t, f, hinj, hmf, hcol⟩ := realization M y₀ p (max P₀ 10) (8 * (K + 1))
    (htyp n (by omega) M y₀ p hF hTpos hTM) hTpos
    (fun t ht => (S07.cond_product_bound _ _ _ _ _ (hUL t ht)).1)
    (fun t ht hty => hodd n N hL8 M y₀ p t hF ht hty
      (hmomO n (by omega) M y₀ p t hF ht S07.cond_product_bound (hUL t ht)))
    (fun t W hW => hJ n N hLC M y₀ p t W hF.slice hW)
    (fun t ht hty J hJt => heven n N hL10 M y₀ p t J hF ht hty hJt
      (even_moment M y₀ p (max P₀ 10) t J hF.slice
        (clock_factor M y₀ p (max P₀ 10) t J hF.slice hJt)
        (hint n (by omega) M y₀ p t hF ht S07.cond_product_bound (hUL t ht)
          (star_mean M y₀ p t hF.slice))))
  exact hall_of_realization M y₀ p t f hF.slice hinj hmf hcol

/-- The input of Lemma 11.2 from a menu with its slice facts. -/
theorem profileInput_of {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (hS : SliceFacts M y₀) (hHost : 2 ^ n ≤ N) :
    ProfileInput n N E X Y κ M.μ M.ν (piRow M y₀) (alphaRow M y₀) :=
  { host := hHost
    μ_supp := M.μ_supp
    ν_supp := M.ν_supp
    avail := M.avail
    π_nonneg := fun i y => (hS.rows i).pi_nonneg y
    π_sum := fun i => (hS.rows i).pi_sum
    π_supp := fun i y h => (hS.rows i).pi_supp y h
    π_cap := fun i y => (hS.rows i).pi_cap y
    α_nonneg := fun i x => (hS.alpha i).nonneg x
    α_sum := fun i => (hS.alpha i).sum_le
    α_supp := fun i x h => (hS.alpha i).supp x h }

/-- P11.1c (11:9–394): the menu (P11.1-menu), the slice facts (P11.1a–b), the compatible balanced profile
(Lemma 11.2 at tolerance `κ/2`, `K = 32/κ`), Lemma 11.3 at exponent `4P + 1`, and the assignment (P11.1d1–d3). -/
theorem linear_jump_core_from_nodes (δ x₀ h₀ : ℚ) (κ : ℝ)
    (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1 / 20000)
    (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1)
    (hh₀ : 0 < h₀) (hh₀1 : h₀ < 1 / 100) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)),
      LargeAt n₀ C₀ n N →
      DiscOne E X Y ((n : ℝ) ^ ((1 : ℝ) - (δ : ℝ) / 16))
        ((n : ℝ) ^ (x₀ : ℝ)) ((n : ℝ) ^ (-(19 : ℝ) / 20)) →
      (∀ (G : Colour) A B, A ⊆ X → B ⊆ Y →
        (A, B) ∉ PCluster G ((1 / 100 : ℚ) : ℝ) (δ : ℝ) n N E) →
      (∀ (G : Colour) A B, A ⊆ Y → B ⊆ X →
        (A, B) ∉ PCluster G ((1 / 100 : ℚ) : ℝ) (δ : ℝ) n N (transposeRel E)) →
      AvailableAt κ
        (PBias (pw ((1 / 100 : ℚ) : ℝ)) (lw ((1 / 100 : ℚ) : ℝ)) (h₀ : ℝ)).toPatch
        n N E X Y → CubeAt n N E := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hx₀R : (0 : ℝ) < x₀ := by exact_mod_cast hx₀
  have hx₀1R : (x₀ : ℝ) < 1 := by exact_mod_cast hx₀1
  have hh₀R : (0 : ℝ) < h₀ := by exact_mod_cast hh₀
  have hh₀1R : (h₀ : ℝ) < 1 / 100 := by simpa using (Rat.cast_lt (K := ℝ)).mpr hh₀1
  have hκ2 : 0 < κ / 2 := by positivity
  have hK : (0 : ℝ) < 16 / (κ / 2) := by positivity
  obtain ⟨n₁, hmenu⟩ := biased_menu (h₀ : ℝ) κ hh₀R hh₀1R hκ
  obtain ⟨n₂, hslice⟩ := slice_facts
  obtain ⟨n₃, hprof⟩ := compatible_profile (δ : ℝ) (x₀ : ℝ) (κ / 2) hδR hδ1 hx₀R hx₀1R hκ2
  obtain ⟨P, hP, n₄, C₄, hassign⟩ := assignment_cube (δ : ℝ) (x₀ : ℝ) (16 / (κ / 2)) hK
  obtain ⟨n₅, htail⟩ := outer_mass_tail (δ : ℝ) (x₀ : ℝ) (16 / (κ / 2)) (4 * P + 1)
    hδR hδ1 hx₀R hx₀1R hK (by linarith)
  refine ⟨max (max n₁ n₂) (max (max n₃ n₄) n₅), max C₄ 1, ?_⟩
  intro n N E X Y hLarge hDisc hXY hYX hAvail
  have hn : max (max n₁ n₂) (max (max n₃ n₄) n₅) ≤ n := hLarge.1
  have hC₀ : (1 : ℝ) ≤ max C₄ 1 := le_max_right _ _
  have hHostR : (2 : ℝ) ^ n ≤ (N : ℝ) := by
    calc
      (2 : ℝ) ^ n = 1 * (2 : ℝ) ^ n := by ring
      _ ≤ max C₄ 1 * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_right hC₀ (by positivity)
      _ ≤ (N : ℝ) := hLarge.2.1
  have hHost : 2 ^ n ≤ N := by exact_mod_cast hHostR
  obtain ⟨M⟩ := hmenu n (by omega) hAvail
  obtain ⟨y₀, hS⟩ := hslice n (by omega) M
  obtain ⟨p, hBal, hComp⟩ := hprof n (by omega) M.G M.μ M.ν (piRow M y₀) (alphaRow M y₀)
    (profileInput_of M y₀ hS hHost) hDisc hXY hYX
  exact hassign n N (S07.largeAt_weaken hLarge (by omega) (le_max_left _ _)) M y₀ p
    ⟨hHost, hLarge.2.2, hS, hBal, hComp, hDisc⟩ (htail n (by omega))

end HypercubeRamsey.S11.Core
