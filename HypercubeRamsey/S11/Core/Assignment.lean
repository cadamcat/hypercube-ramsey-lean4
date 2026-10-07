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
  classical
  intro s
  by_cases hV : ∃ v : EvenRole n, sliceOf v.1 = s
  · obtain ⟨v, hvs⟩ := hV
    by_cases hn0 : n = 0
    · have hpow4 : (0 : ℝ) ^ (-(4 * P)) = 0 := Real.zero_rpow (by nlinarith)
      have hpow2 : (0 : ℝ) ^ (-(2 * P)) = 0 := Real.zero_rpow (by nlinarith)
      have hthreshold : (n : ℝ) ^ (-(2 * P)) = 0 := by simpa [hn0] using hpow2
      have hE : (rawTags M p).expect (fun t => rawFail M y₀ p t v) ≤ 0 := by
        simpa [hn0, hpow4] using hraw v
      have hzero := HypercubeRamsey.Lane_q_s11_tags.pr_pos_eq_zero_of_expect_nonpos
        (rawTags M p) (fun t => rawFail M y₀ p t v)
        (fun t => HypercubeRamsey.Lane_q_s11_tags.rawFail_nonneg M y₀ p t v) hE
      have hsub : ∀ t, T1 M y₀ p P t s → 0 < rawFail M y₀ p t v := by
        intro t ht
        unfold T1 at ht
        rcases ht with ⟨v', hv's, hlarge⟩
        have heq := HypercubeRamsey.Lane_q_s11_tags.rawFail_same_slice M y₀ p t v' v
          (hv's.trans hvs.symm)
        calc
          0 < rawFail M y₀ p t v' := by simpa [hthreshold] using hlarge
          _ = rawFail M y₀ p t v := heq
      calc
        (rawTags M p).pr (fun t => T1 M y₀ p P t s) ≤
            (rawTags M p).pr (fun t => 0 < rawFail M y₀ p t v) :=
          HypercubeRamsey.Clock.finProb_pr_mono (rawTags M p) hsub
        _ = 0 := hzero
        _ ≤ (n : ℝ) ^ (-(2 * P)) := by simpa [hthreshold]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      let a : ℝ := (n : ℝ) ^ (-(2 * P))
      have ha : 0 < a := by dsimp [a]; exact Real.rpow_pos_of_pos hnpos _
      have hsub : ∀ t, T1 M y₀ p P t s → a ≤ rawFail M y₀ p t v := by
        intro t ht
        unfold T1 at ht
        rcases ht with ⟨v', hv's, hlarge⟩
        have heq := HypercubeRamsey.Lane_q_s11_tags.rawFail_same_slice M y₀ p t v' v
          (hv's.trans hvs.symm)
        exact le_of_lt (by simpa [a] using lt_of_lt_of_eq hlarge heq)
      have hmark := FinProb.markov (rawTags M p) (fun t => rawFail M y₀ p t v) a
        (fun t => HypercubeRamsey.Lane_q_s11_tags.rawFail_nonneg M y₀ p t v) ha
      have hpow : (n : ℝ) ^ (-(4 * P)) = a * a := by
        dsimp [a]
        calc
          (n : ℝ) ^ (-(4 * P)) =
              (n : ℝ) ^ ((-(2 * P)) + (-(2 * P))) := by congr 1 <;> ring
          _ = (n : ℝ) ^ (-(2 * P)) * (n : ℝ) ^ (-(2 * P)) :=
            Real.rpow_add hnpos _ _
      calc
        (rawTags M p).pr (fun t => T1 M y₀ p P t s) ≤
            (rawTags M p).pr (fun t => a ≤ rawFail M y₀ p t v) :=
          HypercubeRamsey.Clock.finProb_pr_mono (rawTags M p) hsub
        _ ≤ (rawTags M p).expect (fun t => rawFail M y₀ p t v) / a := hmark
        _ ≤ (n : ℝ) ^ (-(4 * P)) / a := div_le_div_of_nonneg_right (hraw v) ha.le
        _ = (n : ℝ) ^ (-(2 * P)) := by
          rw [hpow]
          dsimp [a]
          field_simp [ne_of_gt ha]
  · have hfalse : ∀ t, ¬ T1 M y₀ p P t s := by
      intro t ht
      unfold T1 at ht
      rcases ht with ⟨v, hvs, hlarge⟩
      exact hV ⟨v, hvs⟩
    calc
      (rawTags M p).pr (fun t => T1 M y₀ p P t s) = 0 := by
        unfold FinProb.pr
        apply Finset.sum_eq_zero
        intro t ht
        simp [hfalse t]
      _ ≤ (n : ℝ) ^ (-(2 * P)) := Real.rpow_nonneg (by positivity) _

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
  classical
  unfold TagLLL11
  refine ⟨32, ?_⟩
  intro n hn N E X Y κ M y₀ p hF hT1 hT2
  have hn32 : 32 ≤ n := hn
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hn32R : (32 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn32
  let q : ℝ := (n : ℝ) ^ (-(2 * P))
  let Δ : ℕ := (n + 1) ^ 2
  let x : ℝ := xTag n P
  have hqpos : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos hnPos _
  have hqle20 : q ≤ (n : ℝ) ^ (-(20 : ℝ)) := by
    dsimp [q]
    apply Real.rpow_le_rpow_of_exponent_le hnOne
    nlinarith
  have hneg20 : (n : ℝ) ^ (-(20 : ℝ)) = ((n : ℝ) ^ (20 : ℕ))⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    change ((n : ℝ) ^ (20 : ℝ))⁻¹ = ((n : ℝ) ^ (20 : ℕ))⁻¹
    exact congrArg Inv.inv (Real.rpow_natCast (n : ℝ) 20)
  have hpowOrder : (n : ℝ) ^ (3 : ℕ) ≤ (n : ℝ) ^ (20 : ℕ) :=
    pow_le_pow_right₀ hnOne (by norm_num : 3 ≤ 20)
  have hqle : q ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹ := by
    calc
      q ≤ (n : ℝ) ^ (-(20 : ℝ)) := hqle20
      _ = ((n : ℝ) ^ (20 : ℕ))⁻¹ := hneg20
      _ ≤ ((n : ℝ) ^ (3 : ℕ))⁻¹ :=
        (inv_le_inv₀ (pow_pos hnPos 20) (pow_pos hnPos 3)).2 hpowOrder
  have hnPlusNat : n + 1 ≤ 2 * n := by omega
  have hnPlusR : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by exact_mod_cast hnPlusNat
  have hDelta : (Δ : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
    dsimp [Δ]
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (n : ℝ) + 1)
      (by positivity : 0 ≤ 2 * (n : ℝ))).2 hnPlusR
    nlinarith [hsq]
  have hDelta4 : 4 * (Δ : ℝ) ≤ 16 * (n : ℝ) ^ 2 := by
    calc
      4 * (Δ : ℝ) ≤ 4 * (4 * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hDelta (by norm_num : (0 : ℝ) ≤ 4)
      _ = 16 * (n : ℝ) ^ 2 := by ring
  have hDeltaX : (Δ : ℝ) * (4 * q) ≤ 1 / 2 := by
    have h4q : 4 * q ≤ 4 * ((n : ℝ) ^ (3 : ℕ))⁻¹ :=
      mul_le_mul_of_nonneg_left hqle (by norm_num)
    calc
      (Δ : ℝ) * (4 * q) ≤ (Δ : ℝ) * (4 * ((n : ℝ) ^ (3 : ℕ))⁻¹) :=
        mul_le_mul_of_nonneg_left h4q (by positivity)
      _ = 4 * (Δ : ℝ) * ((n : ℝ) ^ (3 : ℕ))⁻¹ := by ring
      _ ≤ 16 * (n : ℝ) ^ 2 * ((n : ℝ) ^ (3 : ℕ))⁻¹ :=
        mul_le_mul_of_nonneg_right hDelta4 (by positivity)
      _ = 16 / (n : ℝ) := by
        rw [div_eq_mul_inv]
        field_simp [ne_of_gt hnPos]
      _ ≤ 1 / 2 := by
        apply (div_le_iff₀ hnPos).2
        nlinarith [hn32R]
  have hDeltaOne : (1 : ℝ) ≤ (Δ : ℝ) := by
    dsimp [Δ]
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    exact one_le_pow₀ (by nlinarith [hn32R] : (1 : ℝ) ≤ (n : ℝ) + 1)
  have hxDef : x = 4 * q := by
    dsimp [x, q, xTag]
  have hxNonneg : 0 ≤ x := by rw [hxDef]; positivity
  have hxLeHalf : 4 * q ≤ 1 / 2 := by nlinarith [hDeltaX, hDeltaOne, hqpos.le]
  have hxLtOne : x < 1 := by rw [hxDef]; linarith
  have hpowHalf : (1 / 2 : ℝ) ≤ (1 - 4 * q) ^ Δ := by
    calc
      (1 / 2 : ℝ) ≤ 1 - (Δ : ℝ) * (4 * q) := by nlinarith [hDeltaX]
      _ ≤ (1 - 4 * q) ^ Δ :=
        HypercubeRamsey.Lane_q_s11_tags.one_sub_mul_pow_lower (by positivity)
          (hxLeHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)) Δ
  have hcharge : 2 * q ≤ x * (1 - x) ^ Δ := by
    rw [hxDef]
    calc
      2 * q = (4 * q) * (1 / 2 : ℝ) := by ring
      _ ≤ (4 * q) * (1 - 4 * q) ^ Δ :=
        mul_le_mul_of_nonneg_left hpowHalf (by positivity)
  have hbad (s : OuterWord n) :
      (rawTags M p).pr (fun t => TagBad M y₀ p P t s) ≤ 2 * q := by
    calc
      (rawTags M p).pr (fun t => TagBad M y₀ p P t s) ≤
          (rawTags M p).pr (fun t => T1 M y₀ p P t s) +
            (rawTags M p).pr (fun t => T2 M y₀ t s) := by
              simpa [TagBad] using
                (FinProb.pr_union (rawTags M p)
                  (fun t => T1 M y₀ p P t s) (fun t => T2 M y₀ t s))
      _ ≤ q + q := add_le_add (hT1 s) (hT2 s)
      _ = 2 * q := by ring
  have hdim : Fintype.card (OuterCoord n) ≤ n := by
    rw [HypercubeRamsey.Lane_q_s11_tags.outerCoord_card]
    exact Nat.sub_le _ _
  have houterPlus : (Fintype.card (OuterCoord n) : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hdim 1
  have hball (s : OuterWord n) : ((wordBall s 2).card : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    calc
      ((wordBall s 2).card : ℝ) ≤ ((Fintype.card (OuterCoord n) : ℝ) + 1) ^ 2 :=
        HypercubeRamsey.Lane_q_s11_tags.wordBall_card_two_le s
      _ ≤ ((n : ℝ) + 1) ^ 2 := by
        exact (sq_le_sq₀ (by positivity) (by positivity)).2 houterPlus
  have hballNat (s : OuterWord n) : (wordBall s 2).card ≤ (n + 1) ^ 2 := by
    exact_mod_cast hball s
  refine {
    x_nonneg := hxNonneg
    x_lt_one := hxLtOne
    scope := ?_
    degree := ?_
    prob := ?_ }
  · intro s t t' hagree
    have h1 := HypercubeRamsey.Lane_q_s11_tags.T1_dependsOn_wordBall M y₀ p P s t t' hagree
    have h2 := HypercubeRamsey.Lane_q_s11_tags.T2_dependsOn_wordBall M y₀ s t t' hagree
    have h1' : T1 M y₀ p P t s = T1 M y₀ p P t' s := by simpa using h1
    have h2' : T2 M y₀ t s = T2 M y₀ t' s := by simpa using h2
    change (T1 M y₀ p P t s ∨ T2 M y₀ t s) =
      (T1 M y₀ p P t' s ∨ T2 M y₀ t' s)
    rw [h1', h2']
  · intro s
    let adjacent : Finset (OuterWord n) := Finset.univ.filter fun j =>
      j ≠ s ∧ ¬ Disjoint (wordBall s 1) (wordBall j 1)
    have hsub : adjacent ⊆ wordBall s 2 := by
      intro j hj
      have hjs := (Finset.mem_filter.mp hj).2.2
      rcases Finset.not_disjoint_iff.mp hjs with ⟨u, hus, huj⟩
      have hsu : wordDist s u ≤ 1 := (Finset.mem_filter.mp hus).2
      have hju : wordDist j u ≤ 1 := (Finset.mem_filter.mp huj).2
      have huj' : wordDist u j ≤ 1 := by
        rw [HypercubeRamsey.Lane_q_s11_tags.wordDist_symm]
        exact hju
      simp only [wordBall, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (HypercubeRamsey.Lane_q_s11_tags.wordDist_triangle s u j).trans (by omega)
    have hbound : adjacent.card ≤ (n + 1) ^ 2 :=
      (Finset.card_le_card hsub).trans (hballNat s)
    simpa [adjacent, Δ] using hbound
  · intro s
    change (FinProb.pi (fun _ : OuterWord n => p)).pr (fun t => TagBad M y₀ p P t s) ≤
      x * (1 - x) ^ Δ
    calc
      (FinProb.pi (fun _ : OuterWord n => p)).pr (fun t => TagBad M y₀ p P t s) =
          (rawTags M p).pr (fun t => TagBad M y₀ p P t s) := rfl
      _ ≤ 2 * q := hbad s
      _ ≤ x * (1 - x) ^ Δ := hcharge

/-- P11.1d1(iii), moments (11:364–368).  For pairwise separated words, remove the at most `(n+1)³` tag events
touching each radius-one ball (`cond_product_bound`, factor `2` per word); the raw tags are independent with
`E A_s(z) = N π(z)` and `E B_s(z) = N Σ p_i α_i(z)` (each neighbouring tag integrates its degree ratio to one). -/
theorem tag_moment (δ x₀ K P : ℝ) (hP : 10 ≤ P) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι),
      Fixed11 δ x₀ K n N E X Y κ M y₀ p → S07.CondProductBound → TagLLL11 M y₀ p P →
      TagMoment11 M y₀ p P := by
  classical
  refine ⟨2, ?_⟩
  intro n hn N E X Y κ M y₀ p hF hCB hTagLLL
  have hn2 : 2 ≤ n := hn
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hbaseR : 1 ≤ (n : ℝ) := by linarith
  have hπrow : ∀ i y, 0 ≤ piRow M y₀ i y := fun i y => (hF.slice.rows i).pi_nonneg y
  have hαrow : ∀ i x, 0 ≤ alphaRow M y₀ i x := fun i x => (hF.slice.alpha i).nonneg x
  have hπbar : ∀ y, 0 ≤ piBar M y₀ p y := by
    intro y
    unfold piBar mixW
    exact Finset.sum_nonneg fun i _ => mul_nonneg (p.nonneg i) (hπrow i y)
  have hαbar : ∀ x, 0 ≤ alphaBar M y₀ p x := by
    intro x
    unfold alphaBar mixW
    exact Finset.sum_nonneg fun i _ => mul_nonneg (p.nonneg i) (hαrow i x)
  let Q : OuterWord n → FinProb M.ι := fun _ => p
  let Bad : OuterWord n → (OuterWord n → M.ι) → Prop := fun s t => TagBad M y₀ p P t s
  let sc : OuterWord n → Finset (OuterWord n) := fun s => wordBall s 1
  let good : (OuterWord n → M.ι) → Prop := fun t => ∀ s, ¬ TagBad M y₀ p P t s
  have hInput : S07.LLLInput Q Bad sc (xTag n P) ((n + 1) ^ 2) := by
    simpa [Q, Bad, sc, TagLLL11] using hTagLLL
  have hAvoid := hCB Q Bad sc (xTag n P) ((n + 1) ^ 2) hInput
  have hAvoidPos : 0 < (rawTags M p).pr good := by
    change 0 < (FinProb.pi Q).pr good
    simpa [Q, good, rawTags] using hAvoid.1
  intro z m hm s hsep
  let U : Finset (OuterWord n) :=
    Finset.univ.biUnion fun i : Fin m => wordBall (s i) 1
  let touch : Finset (OuterWord n) := Finset.univ.filter fun r =>
    ¬ Disjoint (wordBall r 1) U
  have htouchSub : touch ⊆ Finset.univ.biUnion fun i : Fin m => wordBall (s i) 2 := by
    intro r hr
    have hnd : ¬ Disjoint (wordBall r 1) U := (Finset.mem_filter.mp hr).2
    rcases Finset.not_disjoint_iff.mp hnd with ⟨u, hur, huU⟩
    rcases Finset.mem_biUnion.mp huU with ⟨i, hi, huBall⟩
    have hru : wordDist r u ≤ 1 := (Finset.mem_filter.mp hur).2
    have hsiu : wordDist (s i) u ≤ 1 := (Finset.mem_filter.mp huBall).2
    have hdist : wordDist r (s i) ≤ 2 := by
      calc
        wordDist r (s i) ≤ wordDist r u + wordDist u (s i) :=
          HypercubeRamsey.Lane_q_s11_tags.wordDist_triangle r u (s i)
        _ ≤ 1 + 1 := add_le_add hru (by
          rw [HypercubeRamsey.Lane_q_s11_tags.wordDist_symm]
          exact hsiu)
        _ = 2 := by norm_num
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [HypercubeRamsey.Lane_q_s11_tags.wordDist_symm]
        exact hdist⟩⟩
  have hOuterCard : Fintype.card (OuterCoord n) ≤ n := by
    rw [HypercubeRamsey.Lane_q_s11_tags.outerCoord_card]
    exact Nat.sub_le _ _
  have hball (i : Fin m) : ((wordBall (s i) 2).card : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by
    have h := HypercubeRamsey.Lane_q_s11_tags.wordBall_card_two_le (s i)
    have hOuterR : (Fintype.card (OuterCoord n) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hOuterCard
    nlinarith [h]
  have htouchCardR : (touch.card : ℝ) ≤ (m : ℝ) * (n + 1 : ℝ) ^ 2 := by
    calc
      (touch.card : ℝ) ≤
          ((Finset.univ.biUnion fun i : Fin m => wordBall (s i) 2).card : ℝ) := by
            exact_mod_cast Finset.card_le_card htouchSub
      _ ≤ ∑ i : Fin m, ((wordBall (s i) 2).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin m, (n + 1 : ℝ) ^ 2 :=
            Finset.sum_le_sum fun i _ => hball i
      _ = (m : ℝ) * (n + 1 : ℝ) ^ 2 := by simp
  have hcastTouch : ((m * (n + 1) ^ 2 : ℕ) : ℝ) =
      (m : ℝ) * (n + 1 : ℝ) ^ 2 := by norm_num
  have htouchCard' : (touch.card : ℝ) ≤ ((m * (n + 1) ^ 2 : ℕ) : ℝ) := by
    rw [hcastTouch]
    exact htouchCardR
  have htouchCard : touch.card ≤ m * (n + 1) ^ 2 := Nat.cast_le.mp htouchCard'
  let q : ℝ := xTag n P
  have hpow : (n : ℝ) ^ (-(2 * P)) ≤ (n : ℝ) ^ (-(20 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hbaseR (by nlinarith [hP])
  have hnegpow : (n : ℝ) ^ (-(18 : ℝ)) ≤ (2 : ℝ) ^ (-(18 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hnR (by norm_num)
  have hpowprod : (n : ℝ) ^ (-(20 : ℝ)) * (n : ℝ) ^ 2 =
      (n : ℝ) ^ (-(18 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity : 0 < (n : ℝ))]
    congr 1 <;> ring
  have hplusSq : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hnegBound : (16 : ℝ) * (n : ℝ) ^ (-(18 : ℝ)) ≤ 1 / 2 := by
    calc
      (16 : ℝ) * (n : ℝ) ^ (-(18 : ℝ)) ≤ 16 * (2 : ℝ) ^ (-(18 : ℝ)) :=
        mul_le_mul_of_nonneg_left hnegpow (by norm_num)
      _ ≤ 1 / 2 := by norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hqDelta : q * ((n + 1) ^ 2 : ℕ) ≤ 1 / 2 := by
    dsimp [q, xTag]
    change 4 * (n : ℝ) ^ (-(2 * P)) * (((n + 1) ^ 2 : ℕ) : ℝ) ≤ 1 / 2
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    calc
      4 * (n : ℝ) ^ (-(2 * P)) * ((n : ℝ) + 1) ^ 2 ≤
          4 * (n : ℝ) ^ (-(20 : ℝ)) * ((n : ℝ) + 1) ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow (by norm_num)) (sq_nonneg ((n : ℝ) + 1))
      _ ≤ 16 * (n : ℝ) ^ (-(18 : ℝ) : ℝ) := by
            calc
              4 * (n : ℝ) ^ (-(20 : ℝ)) * ((n : ℝ) + 1) ^ 2 ≤
                  4 * (n : ℝ) ^ (-(20 : ℝ)) * (4 * (n : ℝ) ^ 2) := by
                    exact mul_le_mul_of_nonneg_left hplusSq
                      (by positivity : 0 ≤ 4 * (n : ℝ) ^ (-(20 : ℝ)))
              _ = 16 * ((n : ℝ) ^ (-(20 : ℝ)) * (n : ℝ) ^ 2) := by ring
              _ = 16 * (n : ℝ) ^ (-(18 : ℝ)) := by rw [hpowprod]
      _ ≤ 1 / 2 := hnegBound
  have hqNonneg : 0 ≤ q := by dsimp [q, xTag]; positivity
  have hnplus : 1 ≤ n + 1 := by omega
  have hDeltaPos : 1 ≤ ((n + 1) ^ 2 : ℕ) := one_le_pow₀ hnplus
  have hDeltaR : 1 ≤ (↑((n + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hDeltaPos
  have hqd : q ≤ q * (↑((n + 1) ^ 2 : ℕ) : ℝ) := by
    calc
      q = q * 1 := by ring
      _ ≤ q * (↑((n + 1) ^ 2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hDeltaR hqNonneg
  have hqLeHalf : q ≤ 1 / 2 := le_trans hqd hqDelta
  have hqLeOne : q ≤ 1 := hqLeHalf.trans (by norm_num)
  have hbern (k : ℕ) : 1 - (k : ℝ) * q ≤ (1 - q) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hbase0 : 0 ≤ 1 - q := by linarith
        have hbase1 : 1 - q ≤ 1 := by linarith
        have hpow0 : 0 ≤ (1 - q) ^ k := pow_nonneg hbase0 _
        have hpow1 : (1 - q) ^ k ≤ 1 := pow_le_one₀ hbase0 hbase1
        calc
          1 - (↑(k + 1) : ℝ) * q = (1 - (k : ℝ) * q) - q := by push_cast; ring
          _ ≤ (1 - q) ^ k - q := sub_le_sub_right ih q
          _ ≤ (1 - q) ^ k - q * (1 - q) ^ k := by
                have hmul := mul_le_mul_of_nonneg_left hpow1 hqNonneg
                nlinarith
          _ = (1 - q) ^ (k + 1) := by rw [pow_succ]; ring
  have hpowDelta : 1 / 2 ≤ (1 - q) ^ ((n + 1) ^ 2) := by
    have h := hbern ((n + 1) ^ 2)
    have hqD : ((↑((n + 1) ^ 2 : ℕ) : ℝ) * q) ≤ 1 / 2 := by nlinarith [hqDelta]
    linarith
  have hbase0 : 0 ≤ 1 - q := by linarith [hqLeOne]
  have hbase1 : 1 - q ≤ 1 := by linarith [hqNonneg]
  have hpowm : (1 / 2 : ℝ) ^ m ≤ (1 - q) ^ touch.card := by
    calc
      (1 / 2 : ℝ) ^ m ≤ ((1 - q) ^ ((n + 1) ^ 2)) ^ m :=
        pow_le_pow_left₀ (by norm_num) hpowDelta m
      _ = (1 - q) ^ (((n + 1) ^ 2) * m) := by rw [pow_mul]
      _ = (1 - q) ^ (m * (n + 1) ^ 2) := by rw [Nat.mul_comm]
      _ ≤ (1 - q) ^ touch.card :=
        pow_le_pow_of_le_one hbase0 hbase1 htouchCard
  have hinv : ((1 - q) ^ touch.card)⁻¹ ≤ (2 : ℝ) ^ m := by
    have hden : 0 < (1 - q) ^ touch.card := pow_pos (by linarith [hqLeHalf] : 0 < 1 - q) _
    have hhalf : 0 < (1 / 2 : ℝ) ^ m := by positivity
    calc
      ((1 - q) ^ touch.card)⁻¹ ≤ ((1 / 2 : ℝ) ^ m)⁻¹ := (inv_le_inv₀ hden hhalf).mpr hpowm
      _ = (2 : ℝ) ^ m := by
        rw [← inv_pow]
        norm_num
  let ω₀ : OuterWord n → M.ι := fun _ => Classical.choice (HypercubeRamsey.Clock.finProb_nonempty p)
  have condMomentBound (Φ : (OuterWord n → M.ι) → ℝ) (hΦ : ∀ t, 0 ≤ Φ t)
      (hdep : FinProb.DependsOn Φ U) (B : ℝ) (hB : 0 ≤ B) (hraw :
        (rawTags M p).expect Φ ≤ B) : (tagLaw M y₀ p P).expect Φ ≤ (2 : ℝ) ^ m * B := by
    have hlocal : ∀ ω, ∑ a : (∀ i : U, M.ι),
        (∏ i : U, p.w (a i)) * Φ (S07.glue U ω a) ≤ B := by
      intro ω
      have hglue := HypercubeRamsey.Lane_q_s11_tags.pi_expect_glue_sum Q U Φ ω hdep
      have hglue' : (rawTags M p).expect Φ =
          ∑ a : (∀ i : U, M.ι), (∏ i : U, p.w (a i)) * Φ (S07.glue U ω a) := by
        simpa [rawTags, Q] using hglue
      rw [← hglue']
      exact hraw
    have h := hAvoid.2 U Φ hΦ B hlocal
    have h' : (S07.condOr (FinProb.pi Q)
        (fun t => ∀ s, ¬ TagBad M y₀ p P t s)).expect Φ ≤
        ((1 - xTag n P) ^ touch.card)⁻¹ * B := by
      simpa [Bad, good, sc, touch] using h
    calc
      (tagLaw M y₀ p P).expect Φ ≤ ((1 - q) ^ touch.card)⁻¹ * B := by
        change (S07.condOr (FinProb.pi Q)
          (fun t => ∀ s, ¬ TagBad M y₀ p P t s)).expect Φ ≤
          ((1 - xTag n P) ^ touch.card)⁻¹ * B
        simpa [q] using h'
      _ ≤ (2 : ℝ) ^ m * B := mul_le_mul_of_nonneg_right hinv hB
  let ΦA : (OuterWord n → M.ι) → ℝ := fun t => ∏ i, compA M y₀ t (s i) z
  have hΦA0 : ∀ t, 0 ≤ ΦA t := by
    intro t
    dsimp [ΦA]
    apply Finset.prod_nonneg
    intro i hi
    unfold compA
    exact mul_nonneg (by positivity) (hπrow (t (s i)) z)
  have hdepA : FinProb.DependsOn ΦA U := by
    intro t t' hagree
    dsimp [ΦA]
    apply Finset.prod_congr rfl
    intro i hi
    unfold compA
    rw [hagree (s i) (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by
      simp [wordBall, wordDist]⟩)]
  have hrawA := HypercubeRamsey.Lane_q_s11_tags.raw_compA_product_mean
    M y₀ p z m s hsep
  have hA := condMomentBound ΦA hΦA0 hdepA
    (((N : ℝ) * piBar M y₀ p z) ^ m)
    (pow_nonneg (mul_nonneg (by positivity) (hπbar z)) m) hrawA.le
  refine ⟨?_, ?_⟩
  · simpa [ΦA] using hA
  · let ΦB : (OuterWord n → M.ι) → ℝ := fun t => ∏ i, compB M y₀ p t (s i) z
    have hcompB0 (t : OuterWord n → M.ι) (i : Fin m) :
        0 ≤ compB M y₀ p t (s i) z := by
      unfold compB
      apply mul_nonneg (mul_nonneg (by positivity) (hαrow (t (s i)) z))
      apply Finset.prod_nonneg
      intro j hj
      apply div_nonneg
      · unfold deg
        apply Finset.sum_nonneg
        intro y hy
        exact mul_nonneg (hπrow (t (flipOuter (s i) j)) y) (by
          unfold hit
          split_ifs <;> norm_num)
      · unfold deg
        apply Finset.sum_nonneg
        intro y hy
        exact mul_nonneg (hπbar y) (by
          unfold hit
          split_ifs <;> norm_num)
    have hΦB0 : ∀ t, 0 ≤ ΦB t := by
      intro t
      dsimp [ΦB]
      exact Finset.prod_nonneg fun i hi => hcompB0 t i
    have hcenterBall (i : Fin m) : s i ∈ wordBall (s i) 1 := by
      simp [wordBall, wordDist]
    have hcenter (i : Fin m) : s i ∈ U := by
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, hcenterBall i⟩
    have hdepB : FinProb.DependsOn ΦB U := by
      intro t t' hagree
      dsimp [ΦB]
      apply Finset.prod_congr rfl
      intro i hi
      apply HypercubeRamsey.Lane_q_s11_tags.compB_dependsOn_wordBall M y₀ p (s i) z t t'
      intro u hu
      exact hagree u (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hu⟩)
    have hrawB := HypercubeRamsey.Lane_q_s11_tags.raw_compB_product_mean_le
      M y₀ p z m s hsep (fun i => hαrow i z) hπrow (hαbar z) hπbar
    have hB := condMomentBound ΦB hΦB0 hdepB
      (((N : ℝ) * alphaBar M y₀ p z) ^ m)
      (pow_nonneg (mul_nonneg (by positivity) (hαbar z)) m) hrawB
    simpa [ΦB] using hB

set_option maxHeartbeats 1000000

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
  classical
  let cA : ℝ := Real.log 2 / 2 - 1 / 50
  let cB : ℝ := Real.log 2 / 200
  let cF : ℝ := Real.log 2
  have hcA : 0 < cA := by
    dsimp [cA]
    nlinarith [Real.log_two_gt_d9]
  have hcB : 0 < cB := by
    dsimp [cB]
    positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hcF : 0 < cF := by
    dsimp [cF]
    exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have htA : Filter.Tendsto
      (fun k : ℕ => (k : ℝ) ^ (3 : ℝ) * Real.exp (-cA * (k : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 : ℝ) cA hcA).comp
      tendsto_natCast_atTop_atTop
  have htB : Filter.Tendsto
      (fun k : ℕ => (k : ℝ) ^ (3 : ℝ) * Real.exp (-cB * (k : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 : ℝ) cB hcB).comp
      tendsto_natCast_atTop_atTop
  have htF : Filter.Tendsto
      (fun k : ℕ => (k : ℝ) * Real.exp (-cF * (k : ℝ)))
      Filter.atTop (nhds 0) := by
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) cF hcF).comp
      tendsto_natCast_atTop_atTop
    have hfun : (fun k : ℕ => (k : ℝ) * Real.exp (-cF * (k : ℝ))) =
        (fun r : ℝ => r ^ (1 : ℝ) * Real.exp (-cF * r)) ∘ Nat.cast := by
      funext k
      simp [Function.comp_def, Real.rpow_one]
    rw [hfun]
    exact ht
  have htDenRaw : Filter.Tendsto
      (fun k : ℕ => (k : ℝ) ^ (-(19 / 20 : ℝ))) Filter.atTop (nhds 0) := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : 0 < (19 : ℝ) / 20)).comp
      tendsto_natCast_atTop_atTop
    have hfun : (fun k : ℕ => (k : ℝ) ^ (-(19 / 20 : ℝ))) =
        (fun r : ℝ => r ^ (-(19 / 20 : ℝ))) ∘ Nat.cast := by
      funext k
      rfl
    rw [hfun]
    exact ht
  have htDen : Filter.Tendsto (fun k : ℕ => bS k) Filter.atTop (nhds 0) := by
    have hfun : (fun k : ℕ => bS k) =
        (fun k : ℕ => (k : ℝ) ^ (-(19 / 20 : ℝ))) := by
      funext k
      unfold bS
      congr 1
      ring
    rw [hfun]
    exact htDenRaw
  obtain ⟨nA, hAevent⟩ := Filter.eventually_atTop.1
    (htA.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  obtain ⟨nB, hBevent⟩ := Filter.eventually_atTop.1
    (htB.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  obtain ⟨nF, hFevent⟩ := Filter.eventually_atTop.1
    (htF.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)))
  obtain ⟨nDen, hDenEvent⟩ := Filter.eventually_atTop.1
    (htDen.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 200)))
  let n₀ := max 40000 (max nA (max nB (max nF nDen)))
  refine ⟨n₀, ?_⟩
  intro n hn N E X Y κ M y₀ p hF hgoodPos hTagMoment
  have hnGeo : 40000 ≤ n := le_trans (le_max_left _ _) hn
  have hnTail : max nA (max nB (max nF nDen)) ≤ n :=
    le_trans (le_max_right _ _) hn
  have hnA : nA ≤ n := le_trans (le_max_left _ _) hnTail
  have hnTailB : max nB (max nF nDen) ≤ n :=
    le_trans (le_max_right _ _) hnTail
  have hnB : nB ≤ n := le_trans (le_max_left _ _) hnTailB
  have hnTailF : max nF nDen ≤ n := le_trans (le_max_right _ _) hnTailB
  have hnF : nF ≤ n := le_trans (le_max_left _ _) hnTailF
  have hnDen : nDen ≤ n := le_trans (le_max_right _ _) hnTailF
  have hsmallAseq : (n : ℝ) ^ (3 : ℝ) * Real.exp (-cA * (n : ℝ)) < 1 / 4 := hAevent n hnA
  have hsmallBseq : (n : ℝ) ^ (3 : ℝ) * Real.exp (-cB * (n : ℝ)) < 1 / 4 := hBevent n hnB
  have hsmallAseqNat : (n : ℝ) ^ (3 : ℕ) * Real.exp (-cA * (n : ℝ)) < 1 / 4 := by
    rw [← Real.rpow_natCast]
    exact hsmallAseq
  have hsmallBseqNat : (n : ℝ) ^ (3 : ℕ) * Real.exp (-cB * (n : ℝ)) < 1 / 4 := by
    rw [← Real.rpow_natCast]
    exact hsmallBseq
  have hsmallFseq : (n : ℝ) * Real.exp (-cF * (n : ℝ)) < 1 / 8 := hFevent n hnF
  have hb : bS n ≤ 1 / 200 := le_of_lt (hDenEvent n hnDen)
  have hInReal : (hIn n : ℝ) ≤ (n : ℝ) / 100 := by
    have hnReal : (10000 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show 10000 ≤ n by omega)
    have hfloor : (hIn n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := by
      unfold hIn
      exact Nat.floor_le (by positivity)
    have hnOne : (1 : ℝ) ≤ (n : ℝ) := by linarith
    have hpow : (n : ℝ) ^ ((1 : ℝ) / 10) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hnOne (by norm_num)
    have hsqrt : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (n : ℝ) / 100 := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [hnReal]
    exact hfloor.trans (hpow.trans hsqrt)
  have hIn100R : 100 * (hIn n : ℝ) ≤ (n : ℝ) := by nlinarith [hInReal]
  have hIn100 : 100 * hIn n ≤ n := by exact_mod_cast hIn100R
  have hInDiv : hIn n ≤ n / 100 := by omega
  have hInnerCard : Fintype.card (InnerCoord n) = hIn n :=
    HypercubeRamsey.Lane_q_s11_tags.innerCoord_card (by omega)
  let d : ℕ := Fintype.card (OuterCoord n)
  have hdEq : d = n - hIn n := by
    dsimp [d]
    exact HypercubeRamsey.Lane_q_s11_tags.outerCoord_card n
  have hk : n / 100 ≤ d := by
    rw [hdEq]
    omega
  have h40k : 40 * (n / 100) ≤ d := by
    have hmod : n % 100 < 100 := Nat.mod_lt _ (by norm_num)
    have hdecomp : n = 100 * (n / 100) + n % 100 := by
      calc
        n = n % 100 + 100 * (n / 100) := (Nat.mod_add_div n 100).symm
        _ = 100 * (n / 100) + n % 100 := Nat.add_comm _ _
    rw [hdEq]
    omega
  have hCardWords : Fintype.card (OuterWord n) = 2 ^ d := by
    simpa [d] using HypercubeRamsey.Lane_q_s11_tags.outerWord_card n
  have hCardWordsPos : 0 < (Fintype.card (OuterWord n) : ℝ) := by positivity
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 2 ≤ n by omega)
  have hOuterHalf : n / 2 ≤ d := by
    have hInHalf := HypercubeRamsey.Lane_q_s11_tags.hIn_le_half (by omega : 4 ≤ n)
    rw [hdEq]
    omega
  have hOuterHalfR : (n : ℝ) / 2 ≤ (d : ℝ) := by
    have hcastSub : (d : ℝ) = (n : ℝ) - (hIn n : ℝ) := by
      rw [hdEq, Nat.cast_sub (by omega)]
    have hInHalfR : (hIn n : ℝ) ≤ (n : ℝ) / 2 := by nlinarith [hInReal]
    rw [hcastSub]
    nlinarith
  let U := OuterWord n
  let Ptag : FinProb (OuterWord n → M.ι) := tagLaw M y₀ p P
  let good : (OuterWord n → M.ι) → Prop := fun t => ∀ s, ¬ TagBad M y₀ p P t s
  let succ : Finset (OuterWord n → M.ι) :=
    Finset.univ.filter fun t => Ptag.w t ≠ 0
  have hweight (t : OuterWord n → M.ι) :
      Ptag.w t = (if good t then (rawTags M p).w t / (rawTags M p).pr good else 0) := by
    by_cases hg : good t
    · simp [Ptag, tagLaw, S07.condOr, FinProb.cond, good, hgoodPos, hg]
    · simp [Ptag, tagLaw, S07.condOr, FinProb.cond, good, hgoodPos, hg]
  have hgateSupport (t : OuterWord n → M.ι) (ht : Ptag.w t ≠ 0) :
      GatedTags M y₀ p P t := by
    have hgood : good t := by
      by_contra hnot
      have hz : Ptag.w t = 0 := by simp [hweight, hnot]
      exact ht hz
    have hraw : (rawTags M p).w t ≠ 0 := by
      by_contra hz
      have hzero : Ptag.w t = 0 := by rw [hweight t]; simp [hgood, hz]
      exact ht hzero
    have hcoords : ∀ s, p.w (t s) ≠ 0 := by
      intro s
      have hprod : (∏ s' : OuterWord n, p.w (t s')) ≠ 0 := by
        change (rawTags M p).w t ≠ 0 at hraw
        simpa [rawTags, FinProb.pi] using hraw
      intro hzero
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ s) hzero)
    exact ⟨hcoords, hgood⟩
  have hsupport : ∀ t, t ∈ succ → GatedTags M y₀ p P t := by
    intro t ht
    exact hgateSupport t (Finset.mem_filter.mp ht).2
  have hsumSupport (Φ : (OuterWord n → M.ι) → ℝ) :
      (∑ t ∈ succ, Ptag.w t * Φ t) ≤ Ptag.expect Φ := by
    unfold FinProb.expect
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ succ)
    intro t ht htnot
    have hz : Ptag.w t = 0 := by
      by_contra hne
      exact htnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    simp [hz]
  let near : U → Finset U := fun u => wordBall u 2
  let fNear : ℝ := ((d : ℝ) + 1) ^ 2 / (Fintype.card U : ℝ)
  have hself : ∀ u : U, u ∈ near u := by
    intro u
    simp [near, wordBall, wordDist]
  have hnear : ∀ u : U, ((near u).card : ℝ) ≤ fNear * Fintype.card U := by
    intro u
    have hball := HypercubeRamsey.Lane_q_s11_tags.wordBall_card_two_le u
    change ((wordBall u 2).card : ℝ) ≤ _
    calc
      ((wordBall u 2).card : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by simpa [d] using hball
      _ = fNear * (Fintype.card U : ℝ) := by
        dsimp [fNear, U]
        field_simp [ne_of_gt hCardWordsPos]
  have hfNear : 0 ≤ fNear := by
    dsimp [fNear]
    positivity
  have hlabels : (Fintype.card (Fin N) : ℝ) ≤ (n : ℝ) * 2 ^ n := by
    calc
      (Fintype.card (Fin N) : ℝ) = (N : ℝ) := by simp
      _ ≤ ((n * 2 ^ n : ℕ) : ℝ) := by exact_mod_cast hF.hostUp
      _ = (n : ℝ) * (2 : ℝ) ^ n := by norm_num [Nat.cast_mul, Nat.cast_pow]
  have hnPos : 0 < n := by omega
  let L_A : ℝ := Real.exp ((n : ℝ) / 50)
  let L_B : ℝ := (2 : ℝ) ^ Fintype.card (InnerCoord n) * (19 / 10 : ℝ) ^ d
  let dA : U → Fin N → ℝ := fun _ y => (N : ℝ) * piBar M y₀ p y
  let dB : U → Fin N → ℝ := fun _ x => (N : ℝ) * alphaBar M y₀ p x
  let ZA : U → Fin N → (OuterWord n → M.ι) → ℝ :=
    fun u y t => compA M y₀ t u y
  let ZB : U → Fin N → (OuterWord n → M.ι) → ℝ :=
    fun u x t => compB M y₀ p t u x
  have hπbar : ∀ y, 0 ≤ piBar M y₀ p y := by
    intro y
    unfold piBar mixW
    exact Finset.sum_nonneg fun j hj => mul_nonneg (p.nonneg j)
      ((hF.slice.rows j).pi_nonneg y)
  have hαbar : ∀ x, 0 ≤ alphaBar M y₀ p x := by
    intro x
    unfold alphaBar mixW
    exact Finset.sum_nonneg fun j hj => mul_nonneg (p.nonneg j)
      ((hF.slice.alpha j).nonneg x)
  have hA0 : ∀ u y t, 0 ≤ ZA u y t := by
    intro u y t
    dsimp [ZA, compA]
    exact mul_nonneg (by positivity) (by
      unfold piRow
      exact (hF.slice.rows (t u)).pi_nonneg y)
  have hB0 : ∀ u x t, 0 ≤ ZB u x t := by
    intro u x t
    dsimp [ZB, compB]
    apply mul_nonneg (mul_nonneg (by positivity) ((hF.slice.alpha (t u)).nonneg x))
    apply Finset.prod_nonneg
    intro j hj
    apply div_nonneg
    · unfold deg
      apply Finset.sum_nonneg
      intro y hy
      exact mul_nonneg ((hF.slice.rows (t (flipOuter u j))).pi_nonneg y)
        (by unfold hit; split_ifs <;> norm_num)
    · unfold deg
      apply Finset.sum_nonneg
      intro y hy
      exact mul_nonneg (hπbar y) (by unfold hit; split_ifs <;> norm_num)
  have hLA : 0 ≤ L_A := by positivity
  have hLB : 0 ≤ L_B := by positivity
  have hZA_L : ∀ u y t, t ∈ succ → ZA u y t ≤ L_A := by
    intro u y t ht
    dsimp [ZA, L_A, compA]
    exact (hF.slice.rows (t u)).pi_cap y
  have hZB_L : ∀ u x t, t ∈ succ → ZB u x t ≤ L_B := by
    intro u x t ht
    dsimp [ZB, L_B]
    exact HypercubeRamsey.Lane_q_s11_tags.compB_cap_of_gated
      M y₀ p hF t (hsupport t ht) u x hb
  have hDA : ∀ y, 0 ≤ (Fintype.card U : ℝ)⁻¹ * ∑ u, dA u y := by
    intro y
    dsimp [dA]
    apply mul_nonneg (inv_nonneg.mpr hCardWordsPos.le)
    exact Finset.sum_nonneg fun u hu => mul_nonneg (by positivity) (hπbar y)
  have hDB : ∀ x, 0 ≤ (Fintype.card U : ℝ)⁻¹ * ∑ u, dB u x := by
    intro x
    dsimp [dB]
    apply mul_nonneg (inv_nonneg.mpr hCardWordsPos.le)
    exact Finset.sum_nonneg fun u hu => mul_nonneg (by positivity) (hαbar x)
  have hmeanA : ∀ y, (Fintype.card U : ℝ)⁻¹ * ∑ u, dA u y ≤ K := by
    intro y
    dsimp [dA, U]
    have hsum : (∑ u : OuterWord n, (N : ℝ) * piBar M y₀ p y) =
        (Fintype.card (OuterWord n) : ℝ) * ((N : ℝ) * piBar M y₀ p y) := by simp
    rw [hsum]
    have hcard : (Fintype.card (OuterWord n) : ℝ) ≠ 0 := ne_of_gt hCardWordsPos
    calc
      (Fintype.card (OuterWord n) : ℝ)⁻¹ *
          ((Fintype.card (OuterWord n) : ℝ) * ((N : ℝ) * piBar M y₀ p y)) =
        (N : ℝ) * piBar M y₀ p y := by field_simp
      _ ≤ K := hF.balanced.1 y
  have hmeanB : ∀ x, (Fintype.card U : ℝ)⁻¹ * ∑ u, dB u x ≤ K := by
    intro x
    dsimp [dB, U]
    have hsum : (∑ u : OuterWord n, (N : ℝ) * alphaBar M y₀ p x) =
        (Fintype.card (OuterWord n) : ℝ) * ((N : ℝ) * alphaBar M y₀ p x) := by simp
    rw [hsum]
    calc
      (Fintype.card (OuterWord n) : ℝ)⁻¹ *
          ((Fintype.card (OuterWord n) : ℝ) * ((N : ℝ) * alphaBar M y₀ p x)) =
        (N : ℝ) * alphaBar M y₀ p x := by field_simp [ne_of_gt hCardWordsPos]
      _ ≤ K := hF.balanced.2 x
  have hsepTag {m : ℕ} (u : Fin m → OuterWord n)
      (hs : ∀ i j : Fin m, j < i → u i ∉ near (u j)) :
      ∀ i j, i ≠ j → 3 ≤ wordDist (u i) (u j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hji
    · have hnot := hs j i hijlt
      have hdist : ¬ wordDist (u i) (u j) ≤ 2 := by
        intro hle
        exact hnot (by simpa [near, wordBall] using hle)
      omega
    · have hnot := hs i j hji
      have hdist : ¬ wordDist (u j) (u i) ≤ 2 := by
        intro hle
        exact hnot (by simpa [near, wordBall] using hle)
      have hrev : 2 < wordDist (u j) (u i) := Nat.lt_of_not_ge hdist
      have hrev' : 2 < wordDist (u i) (u j) := by
        rw [HypercubeRamsey.Lane_q_s11_tags.wordDist_symm]
        exact hrev
      omega
  have hJointA : ∀ y (m : ℕ), m ≤ n → ∀ u : Fin m → U,
      (∀ i j : Fin m, j < i → u i ∉ near (u j)) →
      (∑ t ∈ succ, Ptag.w t * ∏ i, ZA (u i) y t) ≤ 2 ^ m * ∏ i, dA (u i) y := by
    intro y m hm u hnearSep
    have hsep := hsepTag u (by simpa using hnearSep)
    have hmom := hTagMoment y m hm u hsep
    let Φ : (OuterWord n → M.ι) → ℝ := fun t => ∏ i, compA M y₀ t (u i) y
    have hΦ0 : ∀ t, 0 ≤ Φ t := by
      intro t
      dsimp [Φ]
      apply Finset.prod_nonneg
      intro i hi
      unfold compA
      exact mul_nonneg (by positivity) (by
        unfold piRow
        exact (hF.slice.rows (t (u i))).pi_nonneg y)
    have hsum := hsumSupport Φ
    calc
      (∑ t ∈ succ, Ptag.w t * ∏ i, ZA (u i) y t) ≤ Ptag.expect Φ := by
        simpa [Φ, ZA] using hsum
      _ ≤ 2 ^ m * ∏ i, dA (u i) y := by
        simpa [dA] using hmom.1
  have hJointB : ∀ x (m : ℕ), m ≤ n → ∀ u : Fin m → U,
      (∀ i j : Fin m, j < i → u i ∉ near (u j)) →
      (∑ t ∈ succ, Ptag.w t * ∏ i, ZB (u i) x t) ≤ 2 ^ m * ∏ i, dB (u i) x := by
    intro x m hm u hnearSep
    have hsep := hsepTag u (by simpa using hnearSep)
    have hmom := hTagMoment x m hm u hsep
    let Φ : (OuterWord n → M.ι) → ℝ := fun t => ∏ i, compB M y₀ p t (u i) x
    have hΦ0 : ∀ t, 0 ≤ Φ t := by
      intro t
      dsimp [Φ]
      exact Finset.prod_nonneg fun i hi => hB0 (u i) x t
    have hsum := hsumSupport Φ
    calc
      (∑ t ∈ succ, Ptag.w t * ∏ i, ZB (u i) x t) ≤ Ptag.expect Φ := by
        simpa [Φ, ZB] using hsum
      _ ≤ 2 ^ m * ∏ i, dB (u i) x := by
        simpa [dB] using hmom.2
  have hOuterLe : d ≤ n := by
    dsimp [d]
    rw [HypercubeRamsey.Lane_q_s11_tags.outerCoord_card]
    exact Nat.sub_le _ _
  have hlog2Nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hDlog : (n : ℝ) / 2 * Real.log 2 ≤ (d : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hOuterHalfR hlog2Nonneg
  have hExpA : Real.exp (-((d : ℝ) * Real.log 2)) * Real.exp ((n : ℝ) / 50) ≤
      Real.exp (-cA * (n : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [cA]
    nlinarith [hDlog]
  have hCardWordsR : (Fintype.card U : ℝ) = (2 : ℝ) ^ d := by
    rw [hCardWords]
    norm_cast
  have h2pow : (2 : ℝ) ^ d = Real.exp ((d : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ d = (Real.exp (Real.log 2)) ^ d := by rw [Real.exp_log (by norm_num)]
      _ = Real.exp ((d : ℝ) * Real.log 2) := by rw [Real.exp_nat_mul]
  have h2powInv : ((2 : ℝ) ^ d)⁻¹ = Real.exp (-((d : ℝ) * Real.log 2)) := by
    rw [h2pow, ← Real.exp_neg]
  have hAprod : fNear * L_A ≤ ((d : ℝ) + 1) ^ 2 * Real.exp (-cA * (n : ℝ)) := by
    calc
      fNear * L_A = ((d : ℝ) + 1) ^ 2 *
          (Real.exp (-((d : ℝ) * Real.log 2)) * Real.exp ((n : ℝ) / 50)) := by
            dsimp [fNear, L_A, U]
            rw [hCardWordsR, div_eq_mul_inv, h2powInv]
            ring
      _ ≤ ((d : ℝ) + 1) ^ 2 * Real.exp (-cA * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hExpA (sq_nonneg ((d : ℝ) + 1))
  have hdPlusSq : ((d : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
    have hdPlus : (d : ℝ) + 1 ≤ 2 * (n : ℝ) := by
      have hdPlusNat : d + 1 ≤ 2 * n := by omega
      exact_mod_cast hdPlusNat
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ (d : ℝ) + 1)
      (by positivity : 0 ≤ 2 * (n : ℝ))).2 hdPlus
    calc
      ((d : ℝ) + 1) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 := hsq
      _ = 4 * (n : ℝ) ^ 2 := by ring
  have hsmallA : (n : ℝ) * fNear * L_A ≤ 1 := by
    calc
      (n : ℝ) * fNear * L_A = (n : ℝ) * (fNear * L_A) := by ring
      _ ≤ (n : ℝ) * (((d : ℝ) + 1) ^ 2 * Real.exp (-cA * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hAprod (by positivity)
      _ ≤ 4 * (n : ℝ) ^ 3 * Real.exp (-cA * (n : ℝ)) := by
        calc
          (n : ℝ) * (((d : ℝ) + 1) ^ 2 * Real.exp (-cA * (n : ℝ))) ≤
              (n : ℝ) * (4 * (n : ℝ) ^ 2 * Real.exp (-cA * (n : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hdPlusSq (Real.exp_nonneg _)) (by positivity)
          _ = 4 * (n : ℝ) ^ 3 * Real.exp (-cA * (n : ℝ)) := by ring
      _ ≤ 1 := by
        have hscaled : 4 * ((n : ℝ) ^ 3 * Real.exp (-cA * (n : ℝ))) ≤ 1 := by
          calc
            4 * ((n : ℝ) ^ 3 * Real.exp (-cA * (n : ℝ))) ≤ 4 * (1 / 4) :=
              mul_le_mul_of_nonneg_left hsmallAseqNat.le (by norm_num)
            _ = 1 := by norm_num
        calc
          4 * (n : ℝ) ^ 3 * Real.exp (-cA * (n : ℝ)) =
              4 * ((n : ℝ) ^ 3 * Real.exp (-cA * (n : ℝ))) := by rw [mul_assoc]
          _ ≤ 1 := hscaled
  have hpow95 : (19 / 20 : ℝ) ^ 20 ≤ 1 / 2 := by norm_num
  have hpow95_40 : (19 / 20 : ℝ) ^ 40 ≤ 1 / 4 := by
    calc
      (19 / 20 : ℝ) ^ 40 = ((19 / 20 : ℝ) ^ 20) ^ 2 := by rw [← pow_mul]
      _ ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hpow95 2
      _ = 1 / 4 := by norm_num
  have hpow95Nat : ∀ k : ℕ, (19 / 20 : ℝ) ^ (40 * k) ≤ (1 / 4 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.mul_succ]
        have hkNonneg : 0 ≤ (1 / 4 : ℝ) ^ k :=
          pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) k
        calc
          (19 / 20 : ℝ) ^ (40 * k + 40) =
              (19 / 20 : ℝ) ^ (40 * k) * (19 / 20 : ℝ) ^ 40 := by rw [pow_add]
          _ ≤
              (1 / 4 : ℝ) ^ k * (19 / 20 : ℝ) ^ 40 :=
            mul_le_mul_of_nonneg_right ih
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 19 / 20) 40)
          _ ≤ (1 / 4 : ℝ) ^ k * (1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_left hpow95_40 hkNonneg
          _ = (1 / 4 : ℝ) ^ (k + 1) := by rw [pow_succ]
  have hBgeom : (2 : ℝ) ^ hIn n * (19 / 20 : ℝ) ^ d ≤ (1 / 2 : ℝ) ^ (n / 100) := by
    have hInPow : (2 : ℝ) ^ hIn n ≤ (2 : ℝ) ^ (n / 100) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by exact_mod_cast hInDiv)
    have hDpow : (19 / 20 : ℝ) ^ d ≤ (19 / 20 : ℝ) ^ (40 * (n / 100)) :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) h40k
    calc
      (2 : ℝ) ^ hIn n * (19 / 20 : ℝ) ^ d ≤
          (2 : ℝ) ^ (n / 100) * (19 / 20 : ℝ) ^ (40 * (n / 100)) :=
        calc
          (2 : ℝ) ^ hIn n * (19 / 20 : ℝ) ^ d ≤
              (2 : ℝ) ^ (n / 100) * (19 / 20 : ℝ) ^ d :=
            mul_le_mul_of_nonneg_right hInPow (pow_nonneg (by norm_num) d)
          _ ≤ (2 : ℝ) ^ (n / 100) * (19 / 20 : ℝ) ^ (40 * (n / 100)) :=
            mul_le_mul_of_nonneg_left hDpow (by positivity)
      _ ≤ (2 : ℝ) ^ (n / 100) * (1 / 4 : ℝ) ^ (n / 100) :=
        mul_le_mul_of_nonneg_left (hpow95Nat (n / 100)) (by positivity)
      _ = (1 / 2 : ℝ) ^ (n / 100) := by rw [← mul_pow]; norm_num
  have hRatioB : fNear * L_B = ((d : ℝ) + 1) ^ 2 *
      (2 : ℝ) ^ hIn n * (19 / 20 : ℝ) ^ d := by
    have hfrac : (19 / 10 : ℝ) ^ d / (2 : ℝ) ^ d = (19 / 20 : ℝ) ^ d := by
      rw [← div_pow]
      norm_num
    dsimp [fNear, L_B, U]
    rw [hCardWordsR, hInnerCard]
    calc
      (((d : ℝ) + 1) ^ 2 / (2 : ℝ) ^ d) *
          ((2 : ℝ) ^ hIn n * (19 / 10 : ℝ) ^ d) =
        ((d : ℝ) + 1) ^ 2 * (2 : ℝ) ^ hIn n *
          ((19 / 10 : ℝ) ^ d / (2 : ℝ) ^ d) := by
              field_simp [pow_ne_zero d (by norm_num : (2 : ℝ) ≠ 0)] <;> ring_nf
      _ = ((d : ℝ) + 1) ^ 2 * (2 : ℝ) ^ hIn n * (19 / 20 : ℝ) ^ d := by rw [hfrac]
  have hKpow : (n : ℝ) / 200 ≤ (n / 100 : ℕ) := by
    let r : ℕ := n % 100
    have hkpos : 1 ≤ n / 100 := by omega
    have hdecompNat : r + 100 * (n / 100) = n := by
      dsimp [r]
      exact Nat.mod_add_div n 100
    have hremNat : r < 100 := by
      dsimp [r]
      exact Nat.mod_lt n (by norm_num)
    have hnNat : n ≤ 200 * (n / 100) := by omega
    have hnR : (n : ℝ) ≤ (200 : ℝ) * ((n / 100 : ℕ) : ℝ) := by exact_mod_cast hnNat
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 200)).2 (by simpa [mul_comm] using hnR)
  have hhalfRpow : (1 / 2 : ℝ) ^ (n / 100 : ℕ) ≤ Real.exp (-cB * (n : ℝ)) := by
    calc
      (1 / 2 : ℝ) ^ (n / 100 : ℕ) = (1 / 2 : ℝ) ^ ((n / 100 : ℕ) : ℝ) := by
        rw [← Real.rpow_natCast]
      _ ≤ (1 / 2 : ℝ) ^ ((n : ℝ) / 200) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hKpow
      _ = Real.exp (-cB * (n : ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 by
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]]
        dsimp [cB]
        ring
  have hsmallB : (n : ℝ) * fNear * L_B ≤ 1 := by
    have hnNonnegR : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hBgeomScaled : (4 * (n : ℝ) ^ 2) * ((2 : ℝ) ^ hIn n * (19 / 20 : ℝ) ^ d) ≤
        (4 * (n : ℝ) ^ 2) * (1 / 2 : ℝ) ^ (n / 100 : ℕ) :=
      mul_le_mul_of_nonneg_left hBgeom (by positivity)
    have hstepB : (((d : ℝ) + 1) ^ 2 * (2 : ℝ) ^ hIn n) *
        (19 / 20 : ℝ) ^ d ≤
        (4 * (n : ℝ) ^ 2) * ((2 : ℝ) ^ hIn n * (19 / 20 : ℝ) ^ d) := by
      calc
        (((d : ℝ) + 1) ^ 2 * (2 : ℝ) ^ hIn n) * (19 / 20 : ℝ) ^ d ≤
            ((4 * (n : ℝ) ^ 2) * (2 : ℝ) ^ hIn n) * (19 / 20 : ℝ) ^ d := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hdPlusSq (by positivity)) (by positivity)
        _ = (4 * (n : ℝ) ^ 2) * ((2 : ℝ) ^ hIn n * (19 / 20 : ℝ) ^ d) := by
              rw [mul_assoc]
    calc
      (n : ℝ) * fNear * L_B = (n : ℝ) * (fNear * L_B) := by rw [mul_assoc]
      _ = (n : ℝ) * (((d : ℝ) + 1) ^ 2 * (2 : ℝ) ^ hIn n *
            (19 / 20 : ℝ) ^ d) := congrArg (fun z : ℝ => (n : ℝ) * z) hRatioB
      _ ≤ (n : ℝ) * ((4 * (n : ℝ) ^ 2) *
            ((2 : ℝ) ^ hIn n * (19 / 20 : ℝ) ^ d)) :=
              mul_le_mul_of_nonneg_left hstepB hnNonnegR
      _ = (n : ℝ) * (4 * (n : ℝ) ^ 2) *
            ((2 : ℝ) ^ hIn n * (19 / 20 : ℝ) ^ d) := by ring
      _ = (n : ℝ) * ((4 * (n : ℝ) ^ 2) *
            ((2 : ℝ) ^ hIn n * (19 / 20 : ℝ) ^ d)) := by ring
      _ ≤ (n : ℝ) * ((4 * (n : ℝ) ^ 2) * (1 / 2 : ℝ) ^ (n / 100 : ℕ)) :=
            mul_le_mul_of_nonneg_left hBgeomScaled hnNonnegR
      _ = (n : ℝ) * (4 * (n : ℝ) ^ 2) * (1 / 2 : ℝ) ^ (n / 100 : ℕ) := by ring
      _ ≤ 4 * (n : ℝ) ^ 3 * Real.exp (-cB * (n : ℝ)) := by
            calc
              (n : ℝ) * (4 * (n : ℝ) ^ 2) * (1 / 2 : ℝ) ^ (n / 100 : ℕ) =
                  4 * (n : ℝ) ^ 3 * (1 / 2 : ℝ) ^ (n / 100 : ℕ) := by ring
              _ ≤ 4 * (n : ℝ) ^ 3 * Real.exp (-cB * (n : ℝ)) :=
                mul_le_mul_of_nonneg_left hhalfRpow (by positivity)
      _ ≤ 1 := by
        have hscaled : 4 * ((n : ℝ) ^ 3 * Real.exp (-cB * (n : ℝ))) ≤ 1 := by
          calc
            4 * ((n : ℝ) ^ 3 * Real.exp (-cB * (n : ℝ))) ≤ 4 * (1 / 4) :=
              mul_le_mul_of_nonneg_left hsmallBseqNat.le (by norm_num)
            _ = 1 := by norm_num
        calc
          4 * (n : ℝ) ^ 3 * Real.exp (-cB * (n : ℝ)) =
              4 * ((n : ℝ) ^ 3 * Real.exp (-cB * (n : ℝ))) := by rw [mul_assoc]
          _ ≤ 1 := hscaled
  have hfailBound : (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n ≤ 1 / 8 := by
    have hquarterHalf (k : ℕ) : (2 : ℝ) ^ k * (1 / 4 : ℝ) ^ k = (1 / 2 : ℝ) ^ k := by
      calc
        (2 : ℝ) ^ k * (1 / 4 : ℝ) ^ k = (2 * (1 / 4 : ℝ)) ^ k := by rw [← mul_pow]
        _ = (1 / 2 : ℝ) ^ k := by norm_num
    have hhalfExp : (1 / 2 : ℝ) ^ n = Real.exp (-cF * (n : ℝ)) := by
      calc
        (1 / 2 : ℝ) ^ n = (Real.exp (-Real.log 2)) ^ n := by
          congr 1
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          norm_num
        _ = Real.exp ((n : ℝ) * (-Real.log 2)) := by rw [← Real.exp_nat_mul]
        _ = Real.exp (-cF * (n : ℝ)) := by dsimp [cF]; congr 1 <;> ring
    calc
      (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n =
          (n : ℝ) * (1 / 2 : ℝ) ^ n := by
            rw [mul_assoc, hquarterHalf]
      _ = (n : ℝ) * Real.exp (-cF * (n : ℝ)) := by rw [hhalfExp]
      _ ≤ 1 / 8 := le_of_lt hsmallFseq
  let threshold : ℝ := 4 * 2 * (K + 1)
  have hthreshold : threshold = 8 * (K + 1) := by dsimp [threshold]; ring
  let avgA (y : Fin N) (t : OuterWord n → M.ι) : ℝ :=
    (Fintype.card U : ℝ)⁻¹ * ∑ u : U, ZA u y t
  let avgB (x : Fin N) (t : OuterWord n → M.ι) : ℝ :=
    (Fintype.card U : ℝ)⁻¹ * ∑ u : U, ZB u x t
  let badA (t : OuterWord n → M.ι) : Prop := ∃ y, threshold < avgA y t
  let badB (t : OuterWord n → M.ι) : Prop := ∃ x, threshold < avgB x t
  have hselfNear : ∀ u : U, u ∈ near u := hself
  have hnearBound : ∀ u : U, ((near u).card : ℝ) ≤ fNear * Fintype.card U := hnear
  have hlabelBound : (Fintype.card (Fin N) : ℝ) ≤ (n : ℝ) * 2 ^ n := hlabels
  have hmeanA' : ∀ y, (Fintype.card U : ℝ)⁻¹ * ∑ u, dA u y ≤ K := hmeanA
  have hmeanB' : ∀ x, (Fintype.card U : ℝ)⁻¹ * ∑ u, dB u x ≤ K := hmeanB
  have hscA := HypercubeRamsey.scatteredMoments_union_labels Ptag succ ZA hA0 L_A hLA
    hZA_L near hselfNear fNear hfNear hnearBound n hnPos 2 K (by norm_num) hK
    dA (fun u y => mul_nonneg (by positivity) (hπbar y)) hmeanA' hJointA hsmallA hlabelBound
  have hscB := HypercubeRamsey.scatteredMoments_union_labels Ptag succ ZB hB0 L_B hLB
    hZB_L near hselfNear fNear hfNear hnearBound n hnPos 2 K (by norm_num) hK
    dB (fun u x => mul_nonneg (by positivity) (hαbar x)) hmeanB' hJointB hsmallB hlabelBound
  let badAEvent : (OuterWord n → M.ι) → Prop := badA
  let badBEvent : (OuterWord n → M.ι) → Prop := badB
  have hprA : Ptag.pr badAEvent ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    have heq : Ptag.pr badAEvent =
        ∑ t, if t ∈ succ ∧ badAEvent t then Ptag.w t else 0 := by
      unfold FinProb.pr badAEvent
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hs : t ∈ succ
      · simp [hs]
      · have hw : Ptag.w t = 0 := by
          by_contra hne
          exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
        simp [hs, hw]
    rw [heq]
    simpa [badA, avgA, threshold, ZA] using hscA
  have hprB : Ptag.pr badBEvent ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    have heq : Ptag.pr badBEvent =
        ∑ t, if t ∈ succ ∧ badBEvent t then Ptag.w t else 0 := by
      unfold FinProb.pr badBEvent
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hs : t ∈ succ
      · simp [hs]
      · have hw : Ptag.w t = 0 := by
          by_contra hne
          exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
        simp [hs, hw]
    rw [heq]
    simpa [badB, avgB, threshold, ZB] using hscB
  have hbadSub : ∀ t, ¬ Typical11 M y₀ p threshold t → badAEvent t ∨ badBEvent t := by
    intro t ht
    by_cases hA : ∀ y, avgA y t ≤ threshold
    · by_cases hB : ∀ x, avgB x t ≤ threshold
      · exact False.elim (ht ⟨by simpa [Typical11, avgA, ZA, U, hCardWords, d, hthreshold] using hA,
          by simpa [Typical11, avgB, ZB, U, hCardWords, d, hthreshold] using hB⟩)
      · right
        push_neg at hB
        exact hB
    · left
      push_neg at hA
      exact hA
  have hbadPr : Ptag.pr (fun t => ¬ Typical11 M y₀ p threshold t) ≤
      Ptag.pr badAEvent + Ptag.pr badBEvent := by
    calc
      Ptag.pr (fun t => ¬ Typical11 M y₀ p threshold t) ≤
          Ptag.pr (fun t => badAEvent t ∨ badBEvent t) :=
            HypercubeRamsey.Clock.finProb_pr_mono Ptag hbadSub
      _ ≤ Ptag.pr badAEvent + Ptag.pr badBEvent := FinProb.pr_union Ptag badAEvent badBEvent
  have hbadPrTarget : Ptag.pr (fun t => ¬ Typical11 M y₀ p (8 * (K + 1)) t) ≤
      Ptag.pr badAEvent + Ptag.pr badBEvent := by
    simpa [hthreshold] using hbadPr
  calc
    (tagLaw M y₀ p P).pr (fun t => ¬ Typical11 M y₀ p (8 * (K + 1)) t) =
        Ptag.pr (fun t => ¬ Typical11 M y₀ p (8 * (K + 1)) t) := rfl
    _ ≤ Ptag.pr badAEvent + Ptag.pr badBEvent := hbadPrTarget
    _ ≤ 1 / 8 + 1 / 8 := add_le_add (hprA.trans hfailBound) (hprB.trans hfailBound)
    _ = 1 / 4 := by norm_num

set_option maxHeartbeats 200000

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
