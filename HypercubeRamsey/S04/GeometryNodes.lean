import HypercubeRamsey.S04.CoreLemmas
import HypercubeRamsey.S04.GeometryNodes_q_s04_geom
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# L4.1f: marking, eligibility and geometric success

Source: `sections/04-…tex`, lines 300–338; blueprint L4.1f.  The three deterministic nodes give the consequences
of geometric success (`geo_cons`, proved); the three probabilistic nodes bound its failure (`geo_prob`, proved).
-/

namespace HypercubeRamsey.S04

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators

/-- L4.1f, eligibility (04:325–328): with at least `λ/2` present IDs in every site-level ball and marked families of
fewer than `n` sets of at most `T` IDs, at most `2n²T = o(λ)` IDs are forbidden in any level ball of an even site,
leaving at least `λ/3` eligible IDs; eligible IDs are present, at their level and in the radius-`r` ball by
definition.  So eligibility is legal on the even sites (for large `n`). -/
theorem geo_legal (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι), LegalOf M tag := by
  exact HypercubeRamsey.Lane_q_s04_geom.geo_legal_proof hβ hβγ hγ

/-- L4.1f, selection (04:329–331): on good heights every even site has height below `H` and a site-level that is
not bad, so its eligible set has an active ID and the long rule selects one. -/
theorem geo_select {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) : SelectOf M tag := by
  classical
  intro ω hgood a
  let p := hd β γ n
  have ha : a.1 ∈ evenSites n := by
    simp [evenSites, a.2]
  have hga := hgood a.1 ha
  have hh : p.height (evenSites n) (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω)) p.Rlong a.1 < p.H := by
    simpa [p, hd] using hga.1
  let j : Fin (p.H + 1) := ⟨p.height (evenSites n) (ppos ω) (pact ω)
    (elig M tag (ppos ω) (paux ω)) p.Rlong a.1,
      Nat.lt_succ_of_lt hh⟩
  have hbad : ¬ p.Bad (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω)) a.1 j := by
    intro hb
    apply hga.2.1
    exact ⟨by dsimp [j]; exact Nat.lt_succ_of_lt hh, hb⟩
  have hnotInactive : ¬ ∀ ℓ ∈ elig M tag (ppos ω) (paux ω) a.1 j, pact ω ℓ = false := by
    intro hall
    exact hbad (Or.inl hall)
  have hactive : ∃ ℓ ∈ elig M tag (ppos ω) (paux ω) a.1 j, pact ω ℓ = true := by
    by_contra hn
    apply hnotInactive
    intro ℓ hℓ
    cases hA : pact ω ℓ <;> simp_all
  change p.selection (evenSites n) (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω))
    (pties ω) a.1 ≠ none
  simpa [HDParams.selection, HDParams.selectionAt, j, hh, hbad] using hactive

/-- L4.1f, marking (04:306–309, 332–338): around an odd role `u` the heights of its even neighbours (pairwise at
distance two) occupy two consecutive levels `j, j+1` with `j < H`; at an occupied level, a neighbour `v₀` at that
height has a non-bad site-level, and its `(r+2)`-crowd ball contains every ID selected at that level, so at most
`n^b` of them; hence `1 ≤ |D_u| ≤ 2n^b ≤ T` and `D_u` is a candidate at `(u, j)`.  If it were invalid it would meet
the greedy maximal marked family (`greedy_spec`), and the common ID would be forbidden for the neighbour that
selected it, contradicting its eligibility. -/
theorem geo_oddOK {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (_hsel : SelectOf M tag) : OddOKOf M tag := by
  exact HypercubeRamsey.Lane_q_s04_geom.geo_oddOK_proof M tag _hsel

/-- L4.1f: geometric success gives, at every even role, a selected reference meeting the local event `E`, and
valid kernels at all odd roles (04:337–338, 361–362). -/
theorem geo_cons {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (hLeg : LegalOf M tag)
    (hSel : SelectOf M tag) (hOdd : OddOKOf M tag) : GeoCons M tag := by
  intro ω hG
  have hlegal := hLeg ω (fun v l => (hG.counts v l).1) hG.families
  refine ⟨fun a => ?_, hOdd ω hG.heights⟩
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hSel ω hG.heights a)
  refine ⟨c, ⟨hc, ?_, fun j => hOdd ω hG.heights _, fun j v _ l => (hG.counts v l).2⟩⟩
  intro v hv l
  exact hlegal v (Finset.mem_filter.mp hv).1 l

set_option maxHeartbeats 600000
/-- L4.1f, counts (04:311–313; L3.8j on all `2^n` sites): some site-level ball has fewer than `λ/2` or more than
`2λ` present IDs with probability at most `2^{n+1}(H+1) e^{-λ/12} ≤ 1/30`. -/
theorem count_prob (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag),
      (prepLaw M tag q q').pr (fun ω => ¬ ∀ v l,
        lamH n / 2 ≤ (countAt (ppos ω) v l : ℝ) ∧ (countAt (ppos ω) v l : ℝ) ≤ 2 * lamH n) ≤ 1 / 30 := by
  classical
  refine ⟨22 ^ 11, ?_⟩
  intro n hn N E G X Y M tag q q'
  let p := hd β γ n
  have hgeom := HypercubeRamsey.Lane_q_s04_geom.hd_count_parameters hβ hβγ hγ n hn
  have hlam : 0 < p.lam := by
    dsimp [p, hd, lamH]
    positivity
  have hbadSubset : ∀ P : Pos β γ n,
      (¬ ∀ v l, lamH n / 2 ≤ (countAt P v l : ℝ) ∧
          (countAt P v l : ℝ) ≤ 2 * lamH n) →
        ∃ v ∈ (Finset.univ : Finset (CubeVertex n)), ∃ j : Fin (p.H + 1),
          let count := (Finset.univ.filter (fun u : CubeVertex p.d =>
            P (u, j) = true ∧ _root_.hammingDist u v ≤ p.r)).card
          ((count : ℝ) < p.lam / 2 ∨ 2 * p.lam < (count : ℝ)) := by
    intro P hbad
    push_neg at hbad
    obtain ⟨v, l, hcount⟩ := hbad
    refine ⟨v, Finset.mem_univ _, l, ?_⟩
    by_cases hlo : (countAt P v l : ℝ) < lamH n / 2
    · exact Or.inl (by simpa [countAt, p, hd] using hlo)
    · have hlow : lamH n / 2 ≤ (countAt P v l : ℝ) := le_of_not_gt hlo
      have hhi := hcount (by simpa [countAt, p, hd] using hlow)
      exact Or.inr (by simpa [countAt, p, hd] using hhi)
  have hconc := height_position_counts p Finset.univ hlam hgeom.2.1 hgeom.1 hgeom.2.2
  let A : Pos β γ n → Prop := fun P =>
    ¬ ∀ v l, lamH n / 2 ≤ (countAt P v l : ℝ) ∧
      (countAt P v l : ℝ) ≤ 2 * lamH n
  let B : Pos β γ n → Prop := fun P =>
    ∃ v ∈ (Finset.univ : Finset (CubeVertex n)), ∃ j : Fin (p.H + 1),
      let count := (Finset.univ.filter (fun u : CubeVertex p.d =>
        P (u, j) = true ∧ _root_.hammingDist u v ≤ p.r)).card
      ((count : ℝ) < p.lam / 2 ∨ 2 * p.lam < (count : ℝ))
  have hmono : p.posLaw.pr A ≤ p.posLaw.pr B := by
    apply pr_mono p.posLaw
    exact hbadSubset
  have hconc' : p.posLaw.pr B ≤
      2 * ((Finset.univ : Finset (CubeVertex n)).card : ℝ) *
        ((p.H + 1 : ℕ) : ℝ) * Real.exp (-p.lam / 12) := by
    simpa [B] using hconc
  have hmargin : (prepLaw M tag q q').pr (fun ω => A (ppos ω)) = p.posLaw.pr A := by
    change (((p.posLaw.prod (auxLaw M tag q q')).prod p.actLaw).prod p.tieLaw).pr
      (fun ω => A ω.1.1.1) = _
    calc
      _ = ((p.posLaw.prod (auxLaw M tag q q')).prod p.actLaw).pr
          (fun ω => A ω.1.1) :=
        HypercubeRamsey.Lane_q_s04_geom.pr_prod_fst _ _ _
      _ = (p.posLaw.prod (auxLaw M tag q q')).pr (fun ω => A ω.1) :=
        HypercubeRamsey.Lane_q_s04_geom.pr_prod_fst
          (p.posLaw.prod (auxLaw M tag q q')) p.actLaw (fun x => A x.1)
      _ = p.posLaw.pr A := HypercubeRamsey.Lane_q_s04_geom.pr_prod_fst _ _ _
  have htail := HypercubeRamsey.Lane_q_s04_geom.count_tail_bound hβ hβγ hγ n hn
  calc
    (prepLaw M tag q q').pr (fun ω => ¬ ∀ v l,
        lamH n / 2 ≤ (countAt (ppos ω) v l : ℝ) ∧
          (countAt (ppos ω) v l : ℝ) ≤ 2 * lamH n) = p.posLaw.pr A := by
            rw [hmargin]
    _ ≤ p.posLaw.pr B := hmono
    _ ≤ 2 * ((Finset.univ : Finset (CubeVertex n)).card : ℝ) *
        ((p.H + 1 : ℕ) : ℝ) * Real.exp (-p.lam / 12) := hconc'
    _ ≤ 1 / 30 := by
      change 2 * ((Finset.univ : Finset (CubeVertex n)).card : ℝ) *
        ((topH β γ n + 1 : ℕ) : ℝ) * Real.exp (-lamH n / 12) ≤ 1 / 30
      exact htail

/-- L4.1f, families (04:313–323): fix positions and masks with at most `2λ` present IDs per ball; a candidate has
`exp(O(T log n))` choices, invalidity events of disjoint candidates depend on disjoint tuples and are independent,
each of probability at most `exp(-n^{ω/5})` (`ValidProb`), so a marked family of `n` (pairwise disjoint, invalid,
by `greedy_spec`) sets has probability at most `exp(n[O(T log n) - n^{ω/5}])`; a union over odd roles and level
pairs is at most `1/30`. -/
theorem family_prob (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι), ValidProb M tag →
      ∀ (q : XProf M tag) (q' : YProf M tag),
        (prepLaw M tag q q').pr (fun ω => (∀ v l, (countAt (ppos ω) v l : ℝ) ≤ 2 * lamH n) ∧
          ∃ (u : OddRole n) (j : Fin (topH β γ n)), n ≤ (marked M tag (ppos ω) (paux ω) u j).card) ≤ 1 / 30 := by
  classical
  let ε : ℝ := omega4 β γ / 60
  let δ : ℝ := 3 * omega4 β γ / 20
  let C : ℝ := 100 / ε
  have hωpos := omega4_pos hβ hγ
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hGrowthTendsto : Tendsto (fun n : ℕ => (n : ℝ) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδpos).comp tendsto_natCast_atTop_atTop
  have hGrowthEvent : ∀ᶠ n : ℕ in atTop, 2 * C ≤ (n : ℝ) ^ δ :=
    hGrowthTendsto.eventually_ge_atTop (2 * C)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hGrowthEvent
  refine ⟨max 60 n₀, ?_⟩
  intro n hn N E G X Y M tag hValid q q'
  have hn60 : 60 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn₀' : n₀ ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hGrowth : 2 * (100 / (omega4 β γ / 60)) ≤ (n : ℝ) ^ (3 * omega4 β γ / 20) := by
    simpa [C, ε, δ] using hn₀ n hn₀'
  let p := hd β γ n
  let F : Pos β γ n → Aux M tag → Prop := fun P a =>
    (∀ v l, (countAt P v l : ℝ) ≤ 2 * lamH n) ∧
      ∃ u : OddRole n, ∃ j : Fin (topH β γ n), n ≤ (marked M tag P a u j).card
  have hauxBound (P : Pos β γ n) :
      (auxLaw M tag q q').pr (F P) ≤ 1 / 30 := by
    by_cases hupper : ∀ v l, (countAt P v l : ℝ) ≤ 2 * lamH n
    · let MaskPair : FinProb (XMasks M tag × YMasks M tag) :=
        (FinProb.pi q).prod (FinProb.pi q')
      have hbind : (auxLaw M tag q q').pr (F P) =
          ∑ ms, MaskPair.w ms *
            (tupleLaw M tag ms.1).pr (fun W => F P (ms, W)) := by
        simpa [auxLaw, Aux, MaskPair] using
          HypercubeRamsey.Lane_q_s04_geom.bind_pr_eq MaskPair (fun ms => tupleLaw M tag ms.1)
            (fun ms W => F P (ms, W))
      have hcond (ms : XMasks M tag × YMasks M tag) :
          (tupleLaw M tag ms.1).pr (fun W => F P (ms, W)) ≤ 1 / 30 := by
        simpa [F, hupper] using
          HypercubeRamsey.Lane_q_s04_geom.family_tuple_bound hβ hβγ hγ M tag hValid
            P ms.1 ms.2 hupper hn60 hGrowth
      calc
        (auxLaw M tag q q').pr (F P) =
            ∑ ms, MaskPair.w ms * (tupleLaw M tag ms.1).pr (fun W => F P (ms, W)) := hbind
        _ ≤ ∑ ms, MaskPair.w ms * (1 / 30) := by
          apply Finset.sum_le_sum
          intro ms hms
          exact mul_le_mul_of_nonneg_left (hcond ms) (MaskPair.nonneg ms)
        _ = 1 / 30 := by
          rw [← Finset.sum_mul, MaskPair.sum_eq_one]
          ring
    · have hempty : ∀ a : Aux M tag, ¬ F P a := by
        intro a h
        exact hupper h.1
      have hzero : (auxLaw M tag q q').pr (F P) = 0 := by
        unfold FinProb.pr
        simp [hempty]
      rw [hzero]
      norm_num
  have hprodBound :
      (prepLaw M tag q q').pr (fun ω => F (ppos ω) (paux ω)) ≤ 1 / 30 := by
    have hprod : (p.posLaw.prod (auxLaw M tag q q')).pr
        (fun x => F x.1 x.2) ≤ 1 / 30 := by
      rw [HypercubeRamsey.Lane_q_s04_geom.prod_pr_eq]
      calc
        (∑ P, p.posLaw.w P * (auxLaw M tag q q').pr (F P)) ≤
            ∑ P, p.posLaw.w P * (1 / 30) := by
          apply Finset.sum_le_sum
          intro P hP
          exact mul_le_mul_of_nonneg_left (hauxBound P) (p.posLaw.nonneg P)
        _ = 1 / 30 := by
          rw [← Finset.sum_mul, p.posLaw.sum_eq_one]
          ring
    have hmargin : (prepLaw M tag q q').pr (fun ω => F (ppos ω) (paux ω)) =
        (p.posLaw.prod (auxLaw M tag q q')).pr (fun x => F x.1 x.2) := by
      change (((p.posLaw.prod (auxLaw M tag q q')).prod p.actLaw).prod p.tieLaw).pr
        (fun ω => F ω.1.1.1 ω.1.1.2) = _
      calc
        _ = ((p.posLaw.prod (auxLaw M tag q q')).prod p.actLaw).pr
            (fun x => F x.1.1 x.1.2) :=
          HypercubeRamsey.Lane_q_s04_geom.pr_prod_fst _ _ _
        _ = (p.posLaw.prod (auxLaw M tag q q')).pr (fun x => F x.1 x.2) :=
          HypercubeRamsey.Lane_q_s04_geom.pr_prod_fst
            (p.posLaw.prod (auxLaw M tag q q')) p.actLaw (fun x => F x.1 x.2)
    rw [hmargin]
    exact hprod
  simpa [F, p, hd] using hprodBound

/-- L4.1f, heights (04:329–331; L3.8f with `Aux` = masks × tuples and `hd_admissible`, `hdRegime`): eligibility
is defined from positions, masks and tuples before activation, so legal eligibility with bad heights has
probability at most `exp(-n^{1+c}) ≤ 1/30`. -/
theorem height_prob (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag),
      (prepLaw M tag q q').pr (fun ω =>
        (hd β γ n).Legal (ppos ω) (elig M tag (ppos ω) (paux ω)) (evenSites n) ∧
          ¬ (hd β γ n).GoodHeights (evenSites n) (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω))) ≤
        1 / 30 := by
  classical
  obtain ⟨c, hc, n₀, hglobal⟩ :=
    height_selection_global 10 (b0H β γ) (bH β γ) (sigmaH β γ) (zetaH β γ)
      (thetaH β γ) (aH β γ) 1 1 2
      (hd_admissible hβ hβγ hγ) (hdRegime hβ hβγ hγ)
  refine ⟨max n₀ 30, ?_⟩
  intro n hn N E G X Y M tag q q'
  have hn₀ : n₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn30 : 30 ≤ n := le_trans (Nat.le_max_right _ _) hn
  let p := hd β γ n
  let A : ((Pos β γ n × Aux M tag) × Pos β γ n) → Prop := fun x =>
    p.Legal x.1.1 (elig M tag x.1.1 x.1.2) (evenSites n) ∧
      ¬ p.GoodHeights (evenSites n) x.1.1 x.2 (elig M tag x.1.1 x.1.2)
  have hbase : ((p.posLaw.prod (auxLaw M tag q q')).prod p.actLaw).pr A ≤
      Real.exp (-(n : ℝ) ^ (1 + c)) := by
    have hdim₁ : 1 * (p.n : ℝ) ≤ p.d := by simp [p, hd]
    have hdim₂ : (p.d : ℝ) ≤ 1 * (p.n : ℝ) := by simp [p, hd]
    have hreg := hdRegime_ok hβ hβγ hγ n
    have h := hglobal p rfl rfl rfl rfl rfl (by simpa [p] using hn₀)
      hdim₁ hdim₂ hreg (evenSites n) (auxLaw M tag q q') (fun P a => elig M tag P a)
    simpa [A, p, hd, HDParams.posLaw, HDParams.actLaw] using h
  have hmargin :
      (prepLaw M tag q q').pr (fun ω => A ((ppos ω, paux ω), pact ω)) =
        ((p.posLaw.prod (auxLaw M tag q q')).prod p.actLaw).pr A := by
    change (FinProb.prod ((FinProb.prod (p.posLaw) (auxLaw M tag q q')).prod p.actLaw)
      (hd β γ n).tieLaw).pr (fun ω => A ω.1) = _
    exact HypercubeRamsey.Lane_q_s04_geom.pr_prod_fst _ _ _
  have hnreal : (30 : ℝ) ≤ n := by exact_mod_cast hn30
  have hbaseOne : (1 : ℝ) ≤ n := by linarith
  have hc0 : 0 ≤ c := hc.le
  have hpowC : 1 ≤ (n : ℝ) ^ c := Real.one_le_rpow hbaseOne hc0
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ (1 + c) := by
    rw [Real.rpow_add (by positivity) 1 c, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hpowC (show 0 ≤ (n : ℝ) by positivity)]
  have hexp : Real.exp (-((n : ℝ) ^ (1 + c))) ≤ 1 / 30 := by
    calc
      Real.exp (-((n : ℝ) ^ (1 + c))) ≤ Real.exp (-(n : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 / ((n : ℝ) + 1) := by
        rw [Real.exp_neg]
        simpa only [one_div] using
          (one_div_le_one_div_of_le (by positivity) (Real.add_one_le_exp (n : ℝ)))
      _ ≤ 1 / 30 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  calc
    (prepLaw M tag q q').pr (fun ω =>
        (hd β γ n).Legal (ppos ω) (elig M tag (ppos ω) (paux ω)) (evenSites n) ∧
          ¬ (hd β γ n).GoodHeights (evenSites n) (ppos ω) (pact ω)
            (elig M tag (ppos ω) (paux ω))) =
        (prepLaw M tag q q').pr (fun ω => A ((ppos ω, paux ω), pact ω)) := by
          apply congrArg
          funext ω
          simp [A, p]
    _ = ((p.posLaw.prod (auxLaw M tag q q')).prod p.actLaw).pr A := hmargin
    _ ≤ Real.exp (-((n : ℝ) ^ (1 + c))) := hbase
    _ ≤ 1 / 30 := hexp

/-- L4.1f (04:311–338): geometric success fails with probability at most `1/10`. -/
theorem geo_prob (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι), ValidProb M tag → LegalOf M tag →
      ∀ (q : XProf M tag) (q' : YProf M tag),
        (prepLaw M tag q q').pr (fun ω => ¬ GeoSucc M tag ω) ≤ 1 / 10 := by
  obtain ⟨n1, h1⟩ := count_prob β γ hβ hβγ hγ
  obtain ⟨n2, h2⟩ := family_prob β γ hβ hβγ hγ
  obtain ⟨n3, h3⟩ := height_prob β γ hβ hβγ hγ
  refine ⟨max n1 (max n2 n3), ?_⟩
  intro n hn N E G X Y M tag hV hL q q'
  have hA := h1 n (le_trans (le_max_left _ _) hn) M tag q q'
  have hB := h2 n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn) M tag hV q q'
  have hC := h3 n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn) M tag q q'
  set P := prepLaw M tag q q'
  set A : Prep M tag → Prop := fun ω => ¬ ∀ v l,
    lamH n / 2 ≤ (countAt (ppos ω) v l : ℝ) ∧ (countAt (ppos ω) v l : ℝ) ≤ 2 * lamH n with hAdef
  set B : Prep M tag → Prop := fun ω => (∀ v l, (countAt (ppos ω) v l : ℝ) ≤ 2 * lamH n) ∧
    ∃ (u : OddRole n) (j : Fin (topH β γ n)), n ≤ (marked M tag (ppos ω) (paux ω) u j).card with hBdef
  set C : Prep M tag → Prop := fun ω =>
    (hd β γ n).Legal (ppos ω) (elig M tag (ppos ω) (paux ω)) (evenSites n) ∧
      ¬ (hd β γ n).GoodHeights (evenSites n) (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω))
    with hCdef
  have hsub : ∀ ω, ¬ GeoSucc M tag ω → (A ω ∨ B ω) ∨ C ω := by
    intro ω hω
    by_cases hc : ∀ v l,
        lamH n / 2 ≤ (countAt (ppos ω) v l : ℝ) ∧ (countAt (ppos ω) v l : ℝ) ≤ 2 * lamH n
    · by_cases hf : ∀ (u : OddRole n) j, (marked M tag (ppos ω) (paux ω) u j).card < n
      · refine Or.inr ⟨hL ω (fun v l => (hc v l).1) hf, fun hgh => hω ⟨hc, hf, hgh⟩⟩
      · refine Or.inl (Or.inr ⟨fun v l => (hc v l).2, ?_⟩)
        by_contra hno
        apply hf
        intro u j
        by_contra hge
        exact hno ⟨u, j, Nat.le_of_not_lt hge⟩
    · exact Or.inl (Or.inl hc)
  calc P.pr (fun ω => ¬ GeoSucc M tag ω) ≤ P.pr (fun ω => (A ω ∨ B ω) ∨ C ω) := pr_mono P hsub
    _ ≤ P.pr (fun ω => A ω ∨ B ω) + P.pr C := FinProb.pr_union P _ _
    _ ≤ (P.pr A + P.pr B) + P.pr C := by linarith [FinProb.pr_union P A B]
    _ ≤ 1 / 10 := by linarith

end HypercubeRamsey.S04
