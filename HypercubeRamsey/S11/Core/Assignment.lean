import HypercubeRamsey.S11.Core.Experiment
import HypercubeRamsey.S11.Core.Assignment_q_s11_tags
import HypercubeRamsey.S11.Core.Compatibility
import HypercubeRamsey.S07.SmallGridPurity
import HypercubeRamsey.S03.ClockSampling
import HypercubeRamsey.S03.ScatteredMoments

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
  classical
  let a : ℝ := 2 * P + 1
  let b : ℝ := Real.log 2 / 2
  have hb : 0 < b := by
    dsimp [b]
    positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hdecay : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ a * Real.exp (-b * (m : ℝ)))
      Filter.atTop (nhds 0) := by
    exact (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a b hb).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨nTail, hTail⟩ := Filter.eventually_atTop.1
    (hdecay.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨max 4 nTail, ?_⟩
  intro n hn N E X Y κ M y₀ p hF s
  have hn4 : 4 ≤ n := le_trans (le_max_left _ _) hn
  have hnTail : nTail ≤ n := le_trans (le_max_right _ _) hn
  let d : ℕ := Fintype.card (OuterCoord n)
  let H : ℝ := (1 / 8 : ℝ) ^ d
  have hD : (n : ℝ) / 2 ≤ (d : ℝ) := by
    dsimp [d]
    rw [HypercubeRamsey.Lane_q_s11_tags.outerCoord_card]
    have hmul : 2 * hIn n ≤ n := by
      have hh := HypercubeRamsey.Lane_q_s11_tags.hIn_le_half hn4
      omega
    have hmulR : 2 * (hIn n : ℝ) ≤ n := by exact_mod_cast hmul
    rw [Nat.cast_sub (by omega)]
    nlinarith
  have hN : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by exact_mod_cast hF.hostUp
  have hpowprod : (n : ℝ) ^ a * (n : ℝ) ^ (-(2 * P)) = n := by
    have hnpos : 0 < (n : ℝ) := by positivity
    have hinv : (n : ℝ) ^ (2 * P) * (n : ℝ) ^ (-(2 * P)) = 1 := by
      rw [← Real.rpow_add hnpos (2 * P) (-(2 * P))]
      simp
    calc
      (n : ℝ) ^ a * (n : ℝ) ^ (-(2 * P)) =
          ((n : ℝ) ^ (2 * P) * (n : ℝ)) * (n : ℝ) ^ (-(2 * P)) := by
        dsimp [a]
        rw [Real.rpow_add hnpos (2 * P) 1, Real.rpow_one]
      _ = ((n : ℝ) ^ (2 * P) * (n : ℝ) ^ (-(2 * P))) * (n : ℝ) := by ring
      _ = (n : ℝ) := by rw [hinv]; ring
  have hdecayN : (n : ℝ) * Real.exp (-b * (n : ℝ)) ≤ (n : ℝ) ^ (-(2 * P)) := by
    have hpoly := hTail n hnTail
    have hpowNonneg : 0 ≤ (n : ℝ) ^ (-(2 * P)) := Real.rpow_nonneg (by positivity) _
    have hterm : (n : ℝ) * Real.exp (-b * (n : ℝ)) =
        ((n : ℝ) ^ a * Real.exp (-b * (n : ℝ))) * (n : ℝ) ^ (-(2 * P)) := by
      calc
        (n : ℝ) * Real.exp (-b * (n : ℝ)) =
              ((n : ℝ) ^ a * (n : ℝ) ^ (-(2 * P))) * Real.exp (-b * (n : ℝ)) := by
          rw [hpowprod]
        _ = ((n : ℝ) ^ a * Real.exp (-b * (n : ℝ))) * (n : ℝ) ^ (-(2 * P)) := by ring
    calc
      (n : ℝ) * Real.exp (-b * (n : ℝ)) =
          ((n : ℝ) ^ a * Real.exp (-b * (n : ℝ))) * (n : ℝ) ^ (-(2 * P)) := hterm
      _ ≤ 1 * (n : ℝ) ^ (-(2 * P)) := mul_le_mul_of_nonneg_right (le_of_lt hpoly) hpowNonneg
      _ = (n : ℝ) ^ (-(2 * P)) := by ring
  have hgeom : (2 : ℝ) ^ n * H ≤ Real.exp (-b * (n : ℝ)) := by
    have hn2d : n ≤ 2 * d := by exact_mod_cast (by nlinarith : (n : ℝ) ≤ 2 * (d : ℝ))
    have hpow : (2 : ℝ) ^ n * (1 / 8 : ℝ) ^ d ≤ (1 / 2 : ℝ) ^ d := by
      calc
        (2 : ℝ) ^ n * (1 / 8 : ℝ) ^ d ≤ (2 : ℝ) ^ (2 * d) * (1 / 8 : ℝ) ^ d := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.pow_le_pow_right (by omega) hn2d) (by positivity)
        _ = (1 / 2 : ℝ) ^ d := by
          rw [pow_mul]
          rw [← mul_pow]
          norm_num
    have hhalf : (1 / 2 : ℝ) ^ d ≤ Real.exp (-b * (n : ℝ)) := by
      have hhalfExp : (1 / 2 : ℝ) ^ d = Real.exp (-((d : ℝ) * Real.log 2)) := by
        rw [← Real.rpow_natCast]
        rw [Real.rpow_def_of_pos (by norm_num)]
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
        ring
      rw [hhalfExp]
      apply Real.exp_le_exp.mpr
      dsimp [b]
      nlinarith [hD, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    exact hpow.trans hhalf
  let tail (x : Fin N) (t : OuterWord n → M.ι) : Prop :=
    (d : ℝ) / 2 < highCount M y₀ t s x
  let badX (x : Fin N) (t : OuterWord n → M.ι) : Prop :=
    (M.μ (t s)).w x ≠ 0 ∧ tail x t
  let neigh : Finset (OuterWord n) := Finset.univ.image (flipOuter s)
  have hdisj : Disjoint ({s} : Finset (OuterWord n)) neigh := by
    apply Finset.disjoint_left.mpr
    intro z hz1 hz2
    have hzs : z = s := Finset.mem_singleton.mp hz1
    rcases Finset.mem_image.mp hz2 with ⟨j, hj, hjs⟩
    exact (HypercubeRamsey.Lane_q_s11_tags.flipOuter_ne_self s j) (hjs.trans hzs)
  have hcenterDep (i : M.ι) :
      FinProb.DependsOn (fun t : OuterWord n → M.ι => t s = i) {s} := by
    intro t t' hagree
    exact congrArg (fun z => z = i) (hagree s (Finset.mem_singleton_self _))
  have htailDep (x : Fin N) : FinProb.DependsOn (tail x) neigh := by
    intro t t' hagree
    have hcount : highCount M y₀ t s x = highCount M y₀ t' s x := by
      unfold highCount
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hagree (flipOuter s j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)]
    exact congrArg (fun z : ℕ => (d : ℝ) / 2 < z) hcount
  have hcenterProb (i : M.ι) :
      (rawTags M p).pr (fun t => t s = i) = p.w i := by
    simpa [rawTags] using
      (HypercubeRamsey.Clock.pi_pr_coordinate (fun _ : OuterWord n => p) s i)
  have hjoint (x : Fin N) (i : M.ι) :
      (rawTags M p).pr (fun t => t s = i ∧ tail x t) =
        p.w i * (rawTags M p).pr (tail x) := by
    have h := HypercubeRamsey.Lane_q_s11_tags.pi_pr_and_of_disjoint
      (fun _ : OuterWord n => p) (fun t => t s = i) (tail x) {s} neigh
      (hcenterDep i) (htailDep x) hdisj
    change (rawTags M p).pr (fun t => t s = i ∧ tail x t) =
      (rawTags M p).pr (fun t => t s = i) * (rawTags M p).pr (tail x) at h
    rw [hcenterProb i] at h
    exact h
  have hperX (x : Fin N) : (rawTags M p).pr (badX x) ≤ H := by
    let eventI (i : M.ι) (t : OuterWord n → M.ι) : Prop :=
      t s = i ∧ (M.μ i).w x ≠ 0 ∧ tail x t
    have hsubset : ∀ t, badX x t → ∃ i ∈ (Finset.univ : Finset M.ι), eventI i t := by
      intro t ht
      refine ⟨t s, Finset.mem_univ _, ?_⟩
      exact ⟨rfl, ht.1, ht.2⟩
    have hmono := HypercubeRamsey.Clock.finProb_pr_mono (rawTags M p) hsubset
    have hunion := HypercubeRamsey.Clock.finProb_pr_biUnion_le_sum
      (rawTags M p) (Finset.univ : Finset M.ι) eventI
    have hEi (i : M.ι) : (rawTags M p).pr (eventI i) ≤ p.w i * H := by
      by_cases hx : (M.μ i).w x ≠ 0
      · have hEsub : ∀ t, eventI i t → t s = i ∧ tail x t := by
          intro t ht
          exact ⟨ht.1, ht.2.2⟩
        have hEbound := HypercubeRamsey.Clock.finProb_pr_mono (rawTags M p) hEsub
        by_cases hp : p.w i = 0
        · rw [hjoint x i] at hEbound
          simpa [hp] using hEbound
        · have htail := HypercubeRamsey.Lane_q_s11_tags.t2_neighbor_tail M y₀ p s x i
            (hF.compat i hp) hx
          calc
            (rawTags M p).pr (eventI i) ≤ (rawTags M p).pr (fun t => t s = i ∧ tail x t) := hEbound
            _ = p.w i * (rawTags M p).pr (tail x) := hjoint x i
            _ ≤ p.w i * H := mul_le_mul_of_nonneg_left htail (p.nonneg i)
      · have hzero : (rawTags M p).pr (eventI i) = 0 := by simp [eventI, hx, FinProb.pr]
        rw [hzero]
        exact mul_nonneg (p.nonneg i) (by positivity)
    calc
      (rawTags M p).pr (badX x) ≤
          (rawTags M p).pr (fun t => ∃ i ∈ (Finset.univ : Finset M.ι), eventI i t) :=
        HypercubeRamsey.Clock.finProb_pr_mono (rawTags M p) hsubset
      _ ≤ ∑ i ∈ (Finset.univ : Finset M.ι), (rawTags M p).pr (eventI i) := hunion
      _ ≤ ∑ i ∈ (Finset.univ : Finset M.ι), p.w i * H := by
        apply Finset.sum_le_sum
        intro i hi
        exact hEi i
      _ = H := by rw [← Finset.sum_mul, p.sum_eq_one]; ring
  have hT2 : (rawTags M p).pr (fun t => T2 M y₀ t s) ≤ (N : ℝ) * H := by
    have hunion := HypercubeRamsey.Clock.finProb_pr_biUnion_le_sum
      (rawTags M p) (Finset.univ : Finset (Fin N)) badX
    have hT2sub : ∀ t, T2 M y₀ t s → ∃ x ∈ (Finset.univ : Finset (Fin N)), badX x t := by
      intro t ht
      rcases ht with ⟨x, hx, htail⟩
      exact ⟨x, Finset.mem_univ _, hx, htail⟩
    calc
      (rawTags M p).pr (fun t => T2 M y₀ t s) ≤
          (rawTags M p).pr (fun t => ∃ x ∈ (Finset.univ : Finset (Fin N)), badX x t) :=
        HypercubeRamsey.Clock.finProb_pr_mono (rawTags M p) hT2sub
      _ ≤ ∑ x ∈ (Finset.univ : Finset (Fin N)), (rawTags M p).pr (badX x) := hunion
      _ ≤ ∑ x ∈ (Finset.univ : Finset (Fin N)), H := by
        apply Finset.sum_le_sum
        intro x hx
        exact hperX x
      _ = (N : ℝ) * H := by simp
  calc
    (rawTags M p).pr (fun t => T2 M y₀ t s) ≤ (N : ℝ) * H := hT2
    _ ≤ (n : ℝ) ^ (-(2 * P)) := by
      calc
        (N : ℝ) * H ≤ (n : ℝ) * (2 : ℝ) ^ n * H :=
          mul_le_mul_of_nonneg_right hN (by positivity)
        _ = (n : ℝ) * ((2 : ℝ) ^ n * H) := by ring
        _ ≤ (n : ℝ) * Real.exp (-b * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
        _ ≤ (n : ℝ) ^ (-(2 * P)) := hdecayN

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
  sorry

/-- P11.1d3, clock comparison (11:388).  The integrand reads the odd labels on the union of the separated stars'
odd neighbourhoods (at most `n² ≤ n⁴` roles); the clock comparison bounds its law by twice the product of the
odd rows, and the other rows integrate to one. -/
theorem clock_factor {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (P : ℝ) (t : OuterWord n → M.ι)
    (J : (EvenRole n → Fin (kTup n) → Fin N) → FinProb (OddRole n → Fin N)) (hS : SliceFacts M y₀)
    (hJ : ∀ W, GoodPre M y₀ p P t W → ClockOK M y₀ p t W (J W)) : ClockFactor11 M y₀ p P t J := by
  sorry

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
  sorry

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
  sorry

/-- P11.1d3, normalization and Hall (11:393–394).  Every row has mass at least `1/2`; the normalized rows are
probability laws supported on common neighbours of the odd labels (`σ_v(x) ≠ 0` puts `x` in the common-neighbour
set of the internal odd neighbours, the outer factors are hits of the outer neighbours; every cube neighbour of
`v` is an inner or an outer flip), with column sums at most `2 · 1/2`; F-HallEmbed (`cubeAt_of_rows`). -/
theorem hall_of_realization {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι) (t : OuterWord n → M.ι)
    (f : OddRole n → Fin N) (hS : SliceFacts M y₀) (hinj : Function.Injective f)
    (hmf : ∀ v, ¬ MassFail M y₀ p t f v) (hcol : ∀ x, ∑ v, evenRowF M y₀ p t f v x ≤ 1 / 2) :
    CubeAt n N E := by
  sorry

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
