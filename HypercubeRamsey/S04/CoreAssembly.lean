import HypercubeRamsey.S04.GadgetNodes
import HypercubeRamsey.S04.ValidityNodes
import HypercubeRamsey.S04.GeometryNodes
import HypercubeRamsey.S04.PosteriorNodes
import HypercubeRamsey.S04.ProfileNodes
import HypercubeRamsey.S04.LocalityNodes
import HypercubeRamsey.S04.LoadNodes

/-!
# L4.1-core: assembly

Source: `sections/04-…tex`, lines 89–598; blueprint L4.1-core.  The failure probabilities of geometric success
(L4.1f), odd loads (L4.1i), predictive thresholds (L4.1j) and even loads (L4.1k) are at most `1/10` each, so some
history and some injected odd labels pass all tests (`good_outcome`); the even rows are then probability laws on
common `G`-neighbourhoods of the injective odd labels with column sums at most one, and Hall's theorem with the
embedding interface gives the cube (`cube_of_good`).
-/

namespace HypercubeRamsey.S04

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- The averaging step (04:545–553, 590–592): the four failure bounds leave a history in `S_pre` and odd labels in
the support of its injection law with no predictive failure and even column sums at most one. -/
theorem good_outcome {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag)
    (J : Prep M tag → FinProb (OddRole n → Fin N))
    (hgeo : (prepLaw M tag q q').pr (fun ω => ¬ GeoSucc M tag ω) ≤ 1 / 10)
    (hodd : (prepLaw M tag q q').pr (fun ω => ∃ y, 1 / 10 < oddCol M tag ω y) ≤ 1 / 10)
    (hpred : ∑ ω, (prepLaw M tag q q').w ω *
        (if SPre M tag ω then (J ω).pr (fun f => ∃ a, PredFail M tag ω a (nbrLabels f a)) else 0) ≤
      1 / 10)
    (heven : ∑ ω, (prepLaw M tag q q').w ω *
        (if SPre M tag ω then (J ω).pr (fun f => ∃ x, 1 < evenCol M tag ω f x) else 0) ≤ 1 / 10) :
    ∃ ω f, SPre M tag ω ∧ (J ω).w f ≠ 0 ∧ (∀ a, ¬ PredFail M tag ω a (nbrLabels f a)) ∧
      ∀ x, evenCol M tag ω f x ≤ 1 := by
  set P := prepLaw M tag q q' with hPdef
  by_contra hno
  have hcover : ∀ ω, SPre M tag ω →
      1 ≤ (J ω).pr (fun f => ∃ a, PredFail M tag ω a (nbrLabels f a)) +
        (J ω).pr (fun f => ∃ x, 1 < evenCol M tag ω f x) := by
    intro ω hS
    have hsum : (J ω).pr (fun f => (∃ a, PredFail M tag ω a (nbrLabels f a)) ∨
        ∃ x, 1 < evenCol M tag ω f x) = ∑ f, (J ω).w f := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro f _
      by_cases hf : (J ω).w f = 0
      · simp [hf]
      · have hAB : (∃ a, PredFail M tag ω a (nbrLabels f a)) ∨ ∃ x, 1 < evenCol M tag ω f x := by
          by_contra hAB
          rw [not_or] at hAB
          apply hno
          refine ⟨ω, f, hS, hf, fun a ha => hAB.1 ⟨a, ha⟩, fun x => ?_⟩
          by_contra hx
          exact hAB.2 ⟨x, lt_of_not_ge hx⟩
        exact if_pos hAB
    rw [(J ω).sum_eq_one] at hsum
    calc (1 : ℝ) = _ := hsum.symm
      _ ≤ _ := FinProb.pr_union _ _ _
  have hS : P.pr (SPre M tag) ≤ 2 / 10 := by
    calc P.pr (SPre M tag) = ∑ ω, if SPre M tag ω then P.w ω else 0 := rfl
      _ ≤ ∑ ω, (P.w ω *
            (if SPre M tag ω then (J ω).pr (fun f => ∃ a, PredFail M tag ω a (nbrLabels f a)) else 0) +
          P.w ω * (if SPre M tag ω then (J ω).pr (fun f => ∃ x, 1 < evenCol M tag ω f x) else 0)) := by
          apply Finset.sum_le_sum
          intro ω _
          by_cases h : SPre M tag ω
          · simp only [if_pos h]
            have h1 := hcover ω h
            have h2 := P.nonneg ω
            nlinarith
          · simp [h]
      _ = (∑ ω, P.w ω *
            (if SPre M tag ω then (J ω).pr (fun f => ∃ a, PredFail M tag ω a (nbrLabels f a)) else 0)) +
          ∑ ω, P.w ω * (if SPre M tag ω then (J ω).pr (fun f => ∃ x, 1 < evenCol M tag ω f x) else 0) :=
          Finset.sum_add_distrib
      _ ≤ 1 / 10 + 1 / 10 := add_le_add hpred heven
      _ = 2 / 10 := by norm_num
  have hnS : P.pr (fun ω => ¬ SPre M tag ω) ≤ 2 / 10 := by
    calc P.pr (fun ω => ¬ SPre M tag ω) ≤
        P.pr (fun ω => ¬ GeoSucc M tag ω ∨ ∃ y, 1 / 10 < oddCol M tag ω y) := by
          apply pr_mono P
          intro ω h
          by_cases hg : GeoSucc M tag ω
          · right
            by_contra hy
            apply h
            refine ⟨hg, fun y => ?_⟩
            by_contra hy'
            exact hy ⟨y, lt_of_not_ge hy'⟩
          · left
            exact hg
      _ ≤ P.pr (fun ω => ¬ GeoSucc M tag ω) + P.pr (fun ω => ∃ y, 1 / 10 < oddCol M tag ω y) :=
          FinProb.pr_union _ _ _
      _ ≤ 2 / 10 := by linarith
  have htot := pr_add_pr_not P (SPre M tag)
  linarith

/-- Hall and the embedding interface (04:592–597): at a good outcome the even rows are probability laws on common
`G`-neighbourhoods of the injective odd labels, with column sums at most one. -/
theorem cube_of_good {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (hgeo : GeoCons M tag)
    (hrow : EvenRowFacts M tag) (ω : Prep M tag) (f : OddRole n → Fin N) (hS : SPre M tag ω)
    (hinj : Function.Injective f) (hpf : ∀ a, ¬ PredFail M tag ω a (nbrLabels f a))
    (hcol : ∀ x, evenCol M tag ω f x ≤ 1) :
    Nonempty ((cube n).Copy (crossGraph (Hits E G))) := by
  let p : EvenRole n → Fin N → ℝ := fun a x => evenRowAt M tag ω a (nbrLabels f a) x
  have hp0 : ∀ a x, 0 ≤ p a x := fun a x => (hrow ω a _).1 x
  have hp1 : ∀ a, ∑ x, p a x = 1 := by
    intro a
    obtain ⟨c, hc⟩ := (hgeo ω hS.1).1 a
    have hpred : PredOK M tag ω a c (nbrLabels f a) := by
      by_contra hno
      exact hpf a ⟨c, hc.sel_eq, hno⟩
    exact (hrow ω a _).2.2.1 c hc hpred
  have hsupp : ∀ a x, p a x ≠ 0 → ∀ b : OddRole n, (cube n).Adj a.1 b.1 → Hits E G x (f b) := by
    intro a x hx b hab
    obtain ⟨j, rfl⟩ := exists_oddNbr_of_adj a b hab
    exact ((hrow ω a _).2.2.2.1 x hx).1 j
  let L : EvenRole n → Finset (Fin N) := fun a => Finset.univ.filter fun x => p a x ≠ 0
  obtain ⟨fA, hfA, hmem⟩ := exists_injective_of_fractional p L hp0 hp1 (by
      intro a x hx
      by_contra hne
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩)) hcol
  have hedge : ∀ a b, (cube n).Adj a.1 b.1 → Hits E G (fA a) (f b) := by
    intro a b hab
    exact hsupp a (fA a) (Finset.mem_filter.mp (hmem a)).2 b hab
  exact cube_copy_of_parts fA f hfA hinj hedge

/-- L4.1-core (04:89–598), assembled from the Section 4 nodes. -/
theorem l41_core_proof (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) (K : ℝ) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n ≥ n₀, ∀ N,
      LargeHost C₀ n N → ∀ (E : Fin N → Fin N → Prop) (G : Colour)
      (X' Y' : Finset (Fin N)) {ι : Type} [Fintype ι]
      (ρ : FinProb ι) (μ ν : ι → Law N),
      (∀ i, PrepLaw β γ G n N E (μ i) (ν i)) →
      (∀ i, (μ i).SupportedIn X' ∧ (ν i).SupportedIn Y') →
      (∀ x, ∑ i, ρ.w i * (μ i).w x ≤ K / N) →
      (∀ y, ∑ i, ρ.w i * (ν i).w y ≤ K / N) →
      (∀ μ' ν' : Law N,
        μ'.WidthLE (2 * (n : ℝ) ^ β) → ν'.WidthLE (2 * (n : ℝ) ^ γ) →
        dens E G μ' ν' ≤ Real.exp (-(n : ℝ) ^ h4 β γ) →
        ¬ (μ'.SupportedIn X' ∧ ν'.SupportedIn Y')) →
      Nonempty ((OAI.HypercubeRamsey.cube n).Copy
        (OAI.HypercubeRamsey.crossGraph (Hits E G))) := by
  obtain ⟨n1, hKN⟩ := key_nbr_card β γ hβ hβγ hγ
  obtain ⟨n2, hKL⟩ := key_local β γ hβ hβγ hγ
  obtain ⟨n3, hKF⟩ := key_fiber β γ hβ hβγ hγ
  obtain ⟨n4, hTag⟩ := tag_exists β γ K hβ hβγ hγ hK
  obtain ⟨n5, hEL⟩ := entry_low β γ hβ hβγ hγ
  obtain ⟨n6, hEO⟩ := entry_own β γ hβ hβγ hγ
  obtain ⟨n7, hXL⟩ := exposure_low β γ hβ hβγ hγ
  obtain ⟨n8, hOR⟩ := own_ratio β γ hβ hβγ hγ
  obtain ⟨n9, hVP⟩ := valid_prob β γ hβ hβγ hγ
  obtain ⟨n10, hLeg⟩ := geo_legal β γ hβ hβγ hγ
  obtain ⟨n11, hGP⟩ := geo_prob β γ hβ hβγ hγ
  obtain ⟨n12, hOC⟩ := odd_cap β γ hβ hβγ hγ
  obtain ⟨n13, hLB⟩ := lik_bound β γ hβ hβγ hγ
  obtain ⟨n14, hCL⟩ := comm_large β γ hβ hβγ hγ
  obtain ⟨c₃, hc₃, n15, hSB⟩ := select_prob β γ hβ hβγ hγ
  obtain ⟨n16, hMP⟩ := mask_profiles β γ hβ hβγ hγ c₃ hc₃
  obtain ⟨n17, C1, hOL⟩ := odd_load_prob β γ K hβ hβγ hγ hK
  obtain ⟨n18, hInj⟩ := injection_exists β γ hβ hβγ hγ
  obtain ⟨n19, hPF⟩ := pred_fail_prob β γ hβ hβγ hγ
  obtain ⟨n20, C2, hEvL⟩ := even_load_prob β γ K hβ hβγ hγ hK
  refine ⟨n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 + n10 + n11 + n12 + n13 + n14 + n15 + n16 +
    n17 + n18 + n19 + n20, max (max C1 C2) 1, ?_⟩
  intro n hn N hHost E G X' Y' ι _ ρ μ ν hprep hsupp hbalX hbalY hexcl
  choose sX sY pd hP using fun i => prepLaw_iff.mp (hprep i)
  let M : Menu4 β γ G n N E X' Y' :=
    { ι := ι, μ := μ, ν := ν, sX := sX, sY := sY, pd := pd, prep := hP,
      μ_supp := fun i => (hsupp i).1, ν_supp := fun i => (hsupp i).2 }
  have hC1 : LargeHost C1 n N :=
    largeHost_mono hHost (le_trans (le_max_left _ _) (le_max_left _ _))
  have hC2 : LargeHost C2 n N :=
    largeHost_mono hHost (le_trans (le_max_right _ _) (le_max_left _ _))
  have h2n : (2 : ℝ) ^ n ≤ N := by
    have h1 : (1 : ℝ) * 2 ^ n ≤ max (max C1 C2) 1 * 2 ^ n :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    linarith [hHost.1]
  obtain ⟨tag, htag⟩ := hTag n (by omega) (hKF n (by omega)) M ρ hHost.2 ⟨hbalX, hbalY⟩
  have hNoPure : NoPure β γ n N E G X' Y' := hexcl
  have hEntryLow := hEL n (by omega) M hNoPure
  have hEntryOwn := hEO n (by omega) M
  have hExp := hXL n (by omega) M tag (hKN n (by omega)) hEntryLow
  have hOwn := hOR n (by omega) M tag (hKN n (by omega)) hEntryLow hEntryOwn
  have hValid := hVP n (by omega) M tag hExp hOwn
  have hLegal := hLeg n (by omega) M tag
  have hSel := geo_select M tag
  have hOddOK := geo_oddOK M tag hSel
  have hGeoCons := geo_cons M tag hLegal hSel hOddOK
  have hOddCap := hOC n (by omega) (hKN n (by omega)) M tag
  have hRefI := ref_indep M tag
  have hLik := hLB n (by omega) (hKL n (by omega)) M tag
  have hComm := hCL n (by omega) M tag hLik
  have hERF := even_row_facts M tag hComm
  have hSelB := hSB n (by omega) M tag
  obtain ⟨q, q', hProf⟩ := hMP n (by omega) M tag hSelB hERF
  have hEligL := elig_local M tag
  have hSelL := sel_local M tag hEligL
  have hOddL := odd_local M tag hSelL
  have hEvenL := even_local M tag hEligL hSelL hOddL
  have hFac := prep_factor M tag q q'
  have hOddF := odd_factor M tag q q' hFac hOddL
  have hEvenF := even_factor M tag q q' hFac hEvenL
  have hRes := prep_resample M tag q q'
  have hGeo := hGP n (by omega) M tag hValid hLegal q q'
  have hOddLoad := hOL n (by omega) N hC1 M tag q q' htag hProf hOddF hOddCap
  have hInj' := hInj n (by omega) N h2n M tag hGeoCons hOddCap
  let J : Prep M tag → FinProb (OddRole n → Fin N) := fun ω =>
    if h : SPre M tag ω then Classical.choose (hInj' ω h) else oddDrawLaw M tag ω
  have hJ : ∀ ω, SPre M tag ω → InjOK M tag ω (J ω) := by
    intro ω h
    simp only [J, dif_pos h]
    exact Classical.choose_spec (hInj' ω h)
  have hClock := even_clock M tag hGeoCons
  have hPred := hPF n (by omega) M tag q q' J hGeoCons hRefI hRes hJ
  have hEven := hEvL n (by omega) N hC2 M tag q q' J htag hProf hEvenF hClock hERF hJ
  obtain ⟨ω, f, hS, hf, hpf, hcol⟩ := good_outcome M tag q q' J hGeo hOddLoad hPred hEven
  exact cube_of_good M tag hGeoCons hERF ω f hS ((hJ ω hS).1 f hf) hpf hcol

end HypercubeRamsey.S04
