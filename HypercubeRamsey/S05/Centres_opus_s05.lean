import HypercubeRamsey.S05.Centres

/-!
# Lane opus-s05: sub-lemmas for L5.1j, L5.1k (rows) and the L5.1g row locality

`L5_1j` is assembled from the marking eligibility `markElig` (a concrete definition, 05:818–833),
its locality, maximality and probability estimates.  `L5_1k_rows` is assembled from a selection
table `LowTable5` (05:896–985) and the long/short comparison (05:987–1001).  Each `sorry` below is
one open sub-lemma; the two targets are proved from them.
-/

namespace HypercubeRamsey.Setup5.Lane_opus_s05

open Classical OAI.HypercubeRamsey
open scoped BigOperators

set_option synthInstance.maxSize 4096
set_option maxHeartbeats 400000

noncomputable section

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

/-! ## L5.1j -/

section J

variable (X : Setup5 γ K' χ n N E G)

/-- The height device fixed from `α` (05:315–329). -/
def canonHt : X.HeightChoice5 where
  b₀ := X.p.alpha / 10000
  b := X.p.alpha / 2000
  σ := X.p.alpha / 1000000
  ζ := X.p.alpha / 100000
  θ := 1 - X.p.alpha / 100000
  a := X.p.alpha / 20000
  adm := Lane_sol_s05_centres.height_admissible X.p
  regime := Lane_sol_s05_centres.heightRegime X.p
  hθ := by have := X.p.halpha.2; linarith
  hbT := by have := X.p.halpha.1; linarith
  fixed := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The long radius fits the canonical slack. -/
theorem canonHt_slack_large : (canonHt X).hp.Rlong + 32 ≤ Lane_sol_s05_centres.centreSlack X.p n := by
  simp only [HDParams.Rlong, HeightChoice5.hp, canonHt, Lane_sol_s05_centres.centreSlack]
  omega

variable (ht : X.HeightChoice5)

/-- Prospective IDs at a site and level (05:820–824). -/
def prosp (P : ht.hp.Loc → Bool) (s : CubeVertex ht.hp.d) (j : ℕ) : Finset ht.hp.Loc :=
  Finset.univ.filter fun l => P l = true ∧ (l.2 : ℕ) = j ∧ hammingDist l.1 s ≤ ht.hp.r

/-- The record of an odd role for given choices at its even neighbours: the body of
`actualRecordAt` with the selections replaced by `σ` (05:331–343). -/
def recordOf (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc) (σ : EvenRole5 n → Option ht.hp.Loc)
    (y : OddRole5 n) : X.RecordOn ht.hp.Loc :=
  let ℓ := X.g.roleKey (X.p.J n) y.1
  let obs : Finset (ht.hp.Loc × X.Ty) := (evenNbrs y).biUnion fun a =>
    match σ a with
    | some l => {(l, X.g.evenType (X.p.J n) a.1)}
    | none => ∅
  let refs : Finset (ht.hp.Loc × X.Ty × Option X.Key) := (evenNbrs y).biUnion fun a =>
    match σ a with
    | some l =>
      if ℓ ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          ℓ.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome then
        {(l, X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)} else ∅
    | none => ∅
  let mask : Option (ht.hp.Loc × X.Ty × Finset (Fin X.blockBound)) :=
    match ℓ with
    | .inl k =>
      if hex : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ a).isSome then
        let a := Classical.choose hex
        match σ a with
        | some l =>
          some (l, X.g.evenType (X.p.J n) a.1,
            X.firstK (X.hitSet A (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k))
              (X.p.usedBlocks n))
        | none => none
      else none
    | .inr _ => none
  (ℓ, obs, refs, mask)

theorem actualRecordAt_eq (elig : X.CΩ ht → ht.hp.EligMap) (H : X.KeyHist) (ω : X.CΩ ht) (R : ℕ)
    (y : OddRole5 n) :
    X.actualRecordAt elig H ω R y = recordOf X ht H (arraysOf ω) (fun a => X.selAt elig ω R a) y := rfl

/-- `heavyCount` on a given array assignment. -/
def heavyCountOn (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc) (v : EvenRole5 n) (c : X.CRef ht) : ℕ :=
  ∑ i : Fin (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1)),
    if ∃ j ∈ c.2, X.blockIdx _ j = some i then
      (Finset.univ.filter fun e : Fin (X.p.typeSegs n (X.g.evenType (X.p.J n) v.1)) × Fin X.p.q0 =>
        X.PriorHeavy H (X.g.evenType (X.p.J n) v.1)
          (A (c.1, X.g.evenType (X.p.J n) v.1) i e.1 e.2)).card
    else 0

/-- The singleton tests of an ID for an even role: prior-heavy fraction and optional hits (05:820–824). -/
def singletonOK (H : X.KeyHist) (A : X.ArraysOn ht.hp.Loc) (v : EvenRole5 n) (l : ht.hp.Loc) : Prop :=
  let c : X.CRef ht := (l, X.refSubsetOn H A (l, X.g.evenType (X.p.J n) v.1) (X.g.optionalKey (X.p.J n) v.1))
  (heavyCountOn X ht H A v c : ℝ) ≤ X.p.nu0 * (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) ∧
    ∀ k, X.g.optionalKey (X.p.J n) v.1 = some (.inl k) →
      X.p.usedBlocks n ≤ (X.hitSet A (l, X.g.evenType (X.p.J n) v.1) (X.lowCol H.2 k)).card

/-- Failed ID sets at an odd state `b` on levels `j, j+1`: mappings of all neighbouring even states
into prospective IDs with at most `T` IDs whose record fails Step 3 at some role of `b`
(05:826–833). -/
def failSets (H : X.KeyHist) (P : ht.hp.Loc → Bool) (A : X.ArraysOn ht.hp.Loc) (b : X.St.Site) (j : ℕ) :
    Finset (Finset ht.hp.Loc) :=
  ((Finset.univ : Finset (X.St.Site → ht.hp.Loc)).filter fun μ =>
      (∀ t ∈ X.St.neighbors b, μ t ∈ prosp X ht P (X.St.oneHot t) j ∪ prosp X ht P (X.St.oneHot t) (j + 1)) ∧
      ((X.St.neighbors b).image μ).card ≤ X.p.T n ∧
      ∃ y : OddRole5 n, X.St.stateOf y.1 = b ∧
        X.step3FailOn H (recordOf X ht H A (fun a => some (μ (X.St.stateOf a.1))) y) A).image
    fun μ => (X.St.neighbors b).image μ

/-- Marked IDs at a site-level: the union of the maximal disjoint failure families of the incident
stars on the two level pairs containing it (05:828–833). -/
def marks (H : X.KeyHist) (P : ht.hp.Loc → Bool) (A : X.ArraysOn ht.hp.Loc) (s : CubeVertex ht.hp.d)
    (j : ℕ) : Finset ht.hp.Loc :=
  (((Finset.univ.filter fun b : X.St.Site => ∃ t ∈ X.St.neighbors b, X.St.oneHot t = s).biUnion fun b =>
    ((Finset.range (ht.hp.H + 1)).filter fun j' => j' = j ∨ j' + 1 = j).biUnion fun j' =>
      (Lane_sol_s05_centres.markingFamily (failSets X ht H P A b j')).biUnion id)).filter
    fun l => (l.2 : ℕ) = j

/-- Pre-activation eligibility from presence and arrays. -/
def eligOf (H : X.KeyHist) (P : ht.hp.Loc → Bool) (A : X.ArraysOn ht.hp.Loc) : ht.hp.EligMap :=
  fun s j => (prosp X ht P s j).filter fun l =>
    (∀ v : EvenRole5 n, X.siteOf v = s → singletonOK X ht H A v l) ∧ l ∉ marks X ht H P A s j

/-- The marking eligibility of L5.1j. -/
def markElig (H : X.KeyHist) (ω : X.CΩ ht) : ht.hp.EligMap := eligOf X ht H (pos ω) (arraysOf ω)

theorem markElig_preActivation (H : X.KeyHist) (ω ω' : X.CΩ ht)
    (h : ∀ l, (ω l).1 = (ω' l).1 ∧ (ω l).2.2.2 = (ω' l).2.2.2) : markElig X ht H ω = markElig X ht H ω' := by
  have hp : pos ω = pos ω' := funext fun l => (h l).1
  have ha : arraysOf ω = arraysOf ω' := funext fun c => by simp only [arraysOf, arr, (h c.1).2]
  simp only [markElig, hp, ha]

theorem markElig_shape (H : X.KeyHist) (ω : X.CΩ ht) (s : CubeVertex ht.hp.d) (j : Fin (ht.hp.H + 1))
    (l : ht.hp.Loc) (hl : l ∈ markElig X ht H ω s j) :
    pos ω l = true ∧ l.2 = j ∧ hammingDist l.1 s ≤ ht.hp.r := by
  have h := (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2
  exact ⟨h.1, Fin.ext h.2.1, h.2.2⟩

/-- SUB-LEMMA J1 (05:880–887): eligibility at a site-level reads center data within `r + 16`.
Prospective sets and singleton tests read the `r`-ball; incident stars have neighbouring sites
within `8` (`CubeStates5.even_distance`), so their mappings read the `(r+8)`-ball. -/
theorem markElig_local (H : X.KeyHist) (s : CubeVertex ht.hp.d) (j : Fin (ht.hp.H + 1)) :
    FinProb.DependsOn (fun ω : X.CΩ ht => markElig X ht H ω s j)
      (Finset.univ.filter fun l : ht.hp.Loc => hammingDist l.1 s ≤ ht.hp.r + 16) := by
  sorry

/-- SUB-LEMMA J2 (05:855–860, maximality): a mapping of all neighbouring even states of an odd
role into eligible IDs on two consecutive levels with at most `T` IDs, agreeing with the
selections at the role's neighbours, passes Step 3; otherwise its ID set would be a failed set
disjoint from the marked maximal family. -/
theorem markElig_sound (H : X.KeyHist) (ω : X.CΩ ht) (R : ℕ) (y : OddRole5 n)
    (μ : X.St.Site → ht.hp.Loc) (j : ℕ) (hj : j ≤ ht.hp.H)
    (helig : ∀ t ∈ X.St.neighbors (X.St.stateOf y.1), μ t ∈ markElig X ht H ω (X.St.oneHot t) (μ t).2)
    (hlev : ∀ t ∈ X.St.neighbors (X.St.stateOf y.1), ((μ t).2 : ℕ) = j ∨ ((μ t).2 : ℕ) = j + 1)
    (hT : ((X.St.neighbors (X.St.stateOf y.1)).image μ).card ≤ X.p.T n)
    (hsel : ∀ a ∈ evenNbrs y, X.selAt (markElig X ht H) ω R a = some (μ (X.St.stateOf a.1))) :
    ¬ X.step3FailOn H (X.actualRecordAt (markElig X ht H) H ω R y) (arraysOf ω) := by
  sorry

/-- Ball counts `λ/2 .. 2λ` at every site-level (05:835–838). -/
def BallsOK (ω : X.CΩ ht) : Prop :=
  ∀ s ∈ X.sites ht, ∀ j : Fin (ht.hp.H + 1),
    ht.hp.lam / 2 ≤ ((Finset.univ.filter fun u : CubeVertex ht.hp.d =>
        pos ω (u, j) = true ∧ hammingDist u s ≤ ht.hp.r).card : ℝ) ∧
      ((Finset.univ.filter fun u : CubeVertex ht.hp.d =>
        pos ω (u, j) = true ∧ hammingDist u s ≤ ht.hp.r).card : ℝ) ≤ 2 * ht.hp.lam

/-- Small singleton losses: at most `λ/12` prospective IDs fail a singleton test at each
site-level (05:835–838). -/
def SinglesOK (H : X.KeyHist) (ω : X.CΩ ht) : Prop :=
  ∀ s ∈ X.sites ht, ∀ j : ℕ, (((prosp X ht (pos ω) s j).filter fun l =>
    ¬ ∀ v : EvenRole5 n, X.siteOf v = s → singletonOK X ht H (arraysOf ω) v l).card : ℝ) ≤ ht.hp.lam / 12

/-- Every maximal disjoint failure family has fewer than `n` members (05:838–846). -/
def FamiliesOK (H : X.KeyHist) (ω : X.CΩ ht) : Prop :=
  ∀ b j, (Lane_sol_s05_centres.markingFamily (failSets X ht H (pos ω) (arraysOf ω) b j)).card < n

/-- The geometry success event: legal eligibility, a long choice at every even role and local
validity at every odd role (05:835–860). -/
def CentreSuccess (H : X.KeyHist) (ω : X.CΩ ht) : Prop :=
  ht.hp.Legal (pos ω) (markElig X ht H ω) (X.sites ht) ∧
    (∀ v, (X.selLong (markElig X ht H) ω v).isSome) ∧
      ∀ y, X.LocalValidAt ht (markElig X ht) H ω ht.hp.Rlong y

/-- Support and true-target gate at the actual long records (05:874–879). -/
def SupportOK (H : X.KeyHist) (ω : X.CΩ ht) : Prop :=
  ∀ y, (∀ a ∈ evenNbrs y, (X.selLong (markElig X ht H) ω a).isSome) →
    let r := X.actualRecordAt (markElig X ht H) H ω ht.hp.Rlong y
    (∀ c ∈ r.2.1, ∀ i, X.blockWeight H c.2 c.2.2.1 (arraysOf ω c i) ≠ 0) ∧
      0 < X.step3PostOn H r (arraysOf ω) none (H.2 (X.g.roleKey (X.p.J n) y.1)) ∧
      X.candGateOn H r (arraysOf ω) (H.2 (X.g.roleKey (X.p.J n) y.1))

end J

/-- SUB-LEMMA J3 (05:835–838): binomial tails for prospective counts. -/
theorem balls_tail : ∀ p : Params5 γ K' χ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ H : X.KeyHist, (X.centreLaw (canonHt X) H).pr (fun ω => ¬ BallsOK X (canonHt X) ω) ≤
        Real.exp (-Real.sqrt n) / 3 := by
  sorry

/-- SUB-LEMMA J4 (05:820–824,835–838): singleton losses, from independent arrays at distinct IDs
and the per-ID `o(1)` failure probability at good histories. -/
theorem singles_tail : ∀ (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
          (X.centreLaw (canonHt X) H).pr (fun ω => BallsOK X (canonHt X) ω ∧
            ¬ SinglesOK X (canonHt X) H ω) ≤ Real.exp (-Real.sqrt n) / 3 := by
  sorry

/-- SUB-LEMMA J5 (05:838–846): `n` disjoint failures at one star read disjoint independent arrays;
the history's Step 3 rates and the record counts bound them by `exp(-Ω(n k'_j))` or
`exp(-Ω(n s))`, summable over stars and level pairs. -/
theorem families_tail : ∀ (C : ℝ) (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        X.RecordCount C → ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
          (X.centreLaw (canonHt X) H).pr (fun ω => BallsOK X (canonHt X) ω ∧
            ¬ FamiliesOK X (canonHt X) H ω) ≤ Real.exp (-Real.sqrt n) / 3 := by
  sorry

/-- SUB-LEMMA J6 (05:846–849, deterministic): with correct counts, small singleton losses and
fewer than `n` failures per star, marks remove `O(n^2 T)` IDs per site-level and the eligible
sets keep `λ/3` IDs. -/
theorem legal_of_events : ∀ p : Params5 γ K' χ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ (H : X.KeyHist) (ω : X.CΩ (canonHt X)), BallsOK X (canonHt X) ω → SinglesOK X (canonHt X) H ω →
        FamiliesOK X (canonHt X) H ω →
          (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω) (X.sites (canonHt X)) := by
  sorry

/-- SUB-LEMMA J7 (05:851–855, D3.8/L3.8 applied): on legal eligibility, the long height rule
gives good heights with probability `1 - o(1)`. -/
theorem heights_tail : ∀ p : Params5 γ K' χ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ H : X.KeyHist, (X.centreLaw (canonHt X) H).pr (fun ω =>
        (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω) (X.sites (canonHt X)) ∧
          ¬ (canonHt X).hp.GoodHeights (X.sites (canonHt X)) (pos ω) (act ω)
            (markElig X (canonHt X) H ω)) ≤ 1 / 300 := by
  sorry

/-- SUB-LEMMA J8 (05:874–879): raw block support, true path support and the true-target gate
at actual long records hold with probability `1 - o(1)` at good histories. -/
theorem support_tail : ∀ (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
          (X.centreLaw (canonHt X) H).pr (fun ω => ¬ SupportOK X (canonHt X) H ω) ≤ 1 / 300 := by
  sorry

/-- SUB-LEMMA J9 (05:851–860, deterministic): good heights give a choice everywhere on two
consecutive levels around each odd state, the crowd bound gives at most `2n^b ≤ T` IDs, the
singleton tests give hits and heavy fractions, and maximality (`markElig_sound`) gives Step 3. -/
theorem success_of_events : ∀ p : Params5 γ K' χ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ (H : X.KeyHist) (ω : X.CΩ (canonHt X)), X.baseLaw.w H.1 ≠ 0 → X.Step1Pass H.1 →
        (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω) (X.sites (canonHt X)) →
        BallsOK X (canonHt X) ω →
        (canonHt X).hp.GoodHeights (X.sites (canonHt X)) (pos ω) (act ω) (markElig X (canonHt X) H ω) →
        SupportOK X (canonHt X) H ω → CentreSuccess X (canonHt X) H ω := by
  sorry

/-- SUB-LEMMA J10 (union bound over J3–J9): the two probability estimates of L5.1j. -/
theorem markElig_estimates : ∀ (C : ℝ) (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        X.RecordCount C → ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
          (X.centreLaw (canonHt X) H).pr (fun ω =>
              ¬ (canonHt X).hp.Legal (pos ω) (markElig X (canonHt X) H ω) (X.sites (canonHt X))) ≤
            Real.exp (-Real.sqrt n) ∧
          (X.centreLaw (canonHt X) H).pr (fun ω => ¬ CentreSuccess X (canonHt X) H ω) ≤ 1 / 100 := by
  sorry

/-- SUB-LEMMA J11 (05:880–887): local validity at the long radius reads center data within
`r + centreSlack`: neighbouring sites lie within `4√n + 302` of the odd image
(`Lane_sol_s05_centres.adjacent_embedding_upper`), selections read `Rlong + r + 16` around them
(`markElig_local`), and `centreSlack_scope` absorbs both. -/
theorem localValid_local (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (y : OddRole5 n) :
    FinProb.DependsOn (fun ω => X.LocalValidAt (canonHt X) (markElig X (canonHt X)) H ω (canonHt X).hp.Rlong y)
      (X.scopeBall (h := canonHt X) y.1 ((canonHt X).hp.r + Lane_sol_s05_centres.centreSlack X.p n)) := by
  sorry

/-- The short presentation mass for a given height choice and eligibility (as in
`shortPresentationMass`). -/
def shortPresMassOf (X : Setup5 γ K' χ n N E G) (ht : X.HeightChoice5)
    (elig : X.KeyHist → X.CΩ ht → ht.hp.EligMap) (H : X.KeyHist) (y : OddRole5 n)
    (r : X.RecordOn ht.hp.Loc) (a : X.ArraysOn ht.hp.Loc) : ℝ :=
  (X.centreLaw ht H).pr fun ω =>
    X.LocalValidAt ht elig H ω (ht.hp.Rshort (X.p.m n)) y ∧
    X.actualRecordAt (elig H) H ω (ht.hp.Rshort (X.p.m n)) y = r ∧
    ∀ c ∈ r.2.1, arraysOf ω c = a c

/-- SUB-LEMMA J12 (05:991–1001): the short presentation reads low keys only at sign distance
`O(√m)`: the short tube, bounded star distances, `CubeStates5.sign_distance`, and integration of
unread arrays. -/
theorem presentation_local : ∃ Ckey : ℕ, ∀ p : Params5 γ K' χ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ b hi y r a, FinProb.DependsOn
        (fun lo => shortPresMassOf X (canonHt X) (markElig X (canonHt X)) (b, X.joinHidden hi lo) y r a)
        (Finset.univ.filter fun k : X.LowIdx =>
          hammingDist k.2.1 (X.g.sign y.1) ≤ Ckey * Nat.sqrt (X.p.m n)) := by
  sorry

/-- The centre layer built from the marking eligibility. -/
def markLayer (X : Setup5 γ K' χ n N E G)
    (hsmall : (Lane_sol_s05_centres.centreSlack X.p n : ℝ) ≤
      (n : ℝ) ^ (1 - ((canonHt X).ζ - (canonHt X).σ) / 4)) : X.CentreLayer5 where
  ht := canonHt X
  elig := markElig X (canonHt X)
  elig_preActivation := markElig_preActivation X (canonHt X)
  elig_shape := markElig_shape X (canonHt X)
  valid H ω y := X.LocalValidAt (canonHt X) (markElig X (canonHt X)) H ω (canonHt X).hp.Rlong y
  success := CentreSuccess X (canonHt X)
  slack := Lane_sol_s05_centres.centreSlack X.p n
  slack_small := hsmall
  slack_large := canonHt_slack_large X
  elig_local := markElig_local X (canonHt X)
  valid_local := localValid_local X
  success_valid H ω h y := h.2.2 y
  success_legal H ω h := h.1
  success_select H ω h := h.2.1
  valid_select H ω y h := h.2.2.1
  valid_base_support H ω y h := h.1
  valid_step1 H ω y h := h.2.1
  valid_block_support H ω y h := h.2.2.2.2.2.2.2.1
  valid_path_support H ω y h := h.2.2.2.2.2.2.2.2.1
  valid_counts H ω y h := h.2.2.2.1
  valid_T H ω y h := h.2.2.2.2.1
  valid_hits H ω y h := h.2.2.2.2.2.1
  valid_heavy H ω y h a ha c hc := by
    cases hs : X.selLong (markElig X (canonHt X) H) ω a with
    | none => simp [evenRefOf, hs] at hc
    | some l =>
      have hc' : c = (l, X.refSubset H ω a l) := by simpa [evenRefOf, hs] using hc.symm
      subst hc'
      exact h.2.2.2.2.2.2.1 a ha l hs
  valid_gate H ω y h := h.2.2.2.2.2.2.2.2.2.1
  valid_step3 H ω y h := h.2.2.2.2.2.2.2.2.2.2

/-- The canonical slack is eventually sublinear. -/
theorem slack_small_eventually (p : Params5 γ K' χ) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (Lane_sol_s05_centres.centreSlack p n : ℝ) ≤ (n : ℝ) ^ (1 - 9 * p.alpha / 4000000) :=
  Filter.eventually_atTop.mp (Lane_sol_s05_centres.centreSlack_small_eventually p)

theorem canonHt_gap (X : Setup5 γ K' χ n N E G) :
    1 - ((canonHt X).ζ - (canonHt X).σ) / 4 = 1 - 9 * X.p.alpha / 4000000 := by
  simp only [canonHt]
  ring

/-- L5.1j from the sub-lemmas. -/
theorem L5_1j_proof : ∀ (C : ℝ) (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) →
    ∃ Ckey : ℕ, ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
        X.RecordCount C → ∃ L : X.CentreLayer5, X.LowLayer5 L Ckey (cL p.pre1) (cH p.pre1) ∧
          ∀ H : X.KeyHist, X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
            (X.centreLaw L.ht H).pr (fun ω => ¬ L.success H ω) ≤ 1 / 100 := by
  intro C cL cH hc
  obtain ⟨Ckey, hkey⟩ := presentation_local (γ := γ) (K' := K') (χ := χ)
  obtain ⟨R, hR⟩ := markElig_estimates (γ := γ) (K' := K') (χ := χ) C cL cH hc
  refine ⟨Ckey, R, fun p hp => ?_⟩
  obtain ⟨n₁, h₁⟩ := hR p hp
  obtain ⟨n₂, h₂⟩ := hkey p
  obtain ⟨n₃, h₃⟩ := slack_small_eventually p
  refine ⟨max n₁ (max n₂ n₃), fun n hn N E G X hXp hRC => ?_⟩
  have hn₁ : n ≥ n₁ := le_trans (le_max_left _ _) hn
  have hn₂ : n ≥ n₂ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn₃ : n ≥ n₃ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hsmall : (Lane_sol_s05_centres.centreSlack X.p n : ℝ) ≤
      (n : ℝ) ^ (1 - ((canonHt X).ζ - (canonHt X).σ) / 4) := by
    rw [canonHt_gap X, hXp]
    exact h₃ n hn₃
  refine ⟨markLayer X hsmall, ?_, ?_⟩
  · exact
      { valid_eq := fun H ω y => Iff.rfl
        presentation_local := fun b hi y r a => h₂ n hn₂ N E G X hXp b hi y r a
        size_failure := fun H hH => (h₁ n hn₁ N E G X hXp hRC H hH).1 }
  · intro H hH
    exact (h₁ n hn₁ N E G X hXp hRC H hH).2

/-! ## L5.1g rows: the remaining locality -/

/-- SUB-LEMMA G1 (05:592–605,880–887): at a valid high role, the actual long record and its
observed arrays are determined by the center data in the role's scope.
**Status:** not derivable from `CentreLayer5` alone when an even neighbour's site is farther
than `16` from the odd image: `CubeStates5` bounds only even-to-even distances (`even_distance`),
and the general adjacent bound is `4√n + 302`, while `slack_large` only gives `Rlong + 32`.
Needs either a constant odd-to-even one-hot bound in `CubeStates5` (TeX 05:309–312) or a
`CentreLayer5` slack field covering the adjacent distance (supplied by `centreSlack`). -/
theorem highRecord_local (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (H : X.KeyHist)
    (y : OddRole5 n) (ω ω' : X.CΩ L.ht)
    (hω : ∀ l ∈ X.scopeBall (h := L.ht) y.1 (L.ht.hp.r + L.slack), ω l = ω' l)
    (hv : L.valid H ω y) (hv' : L.valid H ω' y) (hy : ¬ X.g.low (X.p.J n) y.1) :
    X.actualRecord (L.elig H) H ω y = X.actualRecord (L.elig H) H ω' y ∧
      ∀ c ∈ (X.actualRecord (L.elig H) H ω y).2.1, arraysOf ω c = arraysOf ω' c := by
  sorry

/-! ## L5.1k rows -/

section K

variable (X : Setup5 γ K' χ n N E G)

/-- The selection table and the rows it defines at every consultation radius (05:896–985).
`rowAt R` is the row computed with consultation radius `R` from the short-rule table; the
long row is `rowAt Rlong`, the proxy row `rowAt Rshort`. -/
structure LowTable5 (L : X.CentreLayer5) (Cloc : ℕ) where
  Data : X.Base → X.HighHid → OddRole5 n → Type
  dataFintype : ∀ b hi y, Fintype (Data b hi y)
  selExp : ∀ b hi y (lo : X.LowHid), @SelectionExperiment5 (Fin N) (Data b hi y) _ (dataFintype b hi y)
  selExp_prior : ∀ b hi y lo, X.g.low (X.p.J n) y.1 →
    (selExp b hi y lo).prior = X.prior b (X.g.roleKey (X.p.J n) y.1)
  selExp_records : ∀ b hi y lo, Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1))) *
    (selExp b hi y lo).recordBound ≤ 1
  rowAt : ℕ → X.KeyHist → X.CΩ L.ht → OddRole5 n → X.OddOut → ℝ
  /-- Equal neighbouring choices give equal rows (05:880–887,987–995). -/
  rowAt_congr : ∀ R R' H ω y, (∀ a ∈ evenNbrs y, X.selAt (L.elig H) ω R a = X.selAt (L.elig H) ω R' a) →
    rowAt R H ω y = rowAt R' H ω y
  rowAt_nonneg : ∀ R H ω y o, 0 ≤ rowAt R H ω y o
  rowAt_high : ∀ R H ω y o, ¬ X.g.low (X.p.J n) y.1 → rowAt R H ω y o = 0
  rowAt_cap : ∀ R H ω y o, (N : ℝ) * rowAt R H ω y o ≤ Real.exp (X.p.DL n)
  long_index : ∀ H ω y o, (o.1 : ℕ) ≠ 0 → rowAt L.ht.hp.Rlong H ω y o = 0
  long_invalid : ∀ H ω y o, ¬ L.valid H ω y → rowAt L.ht.hp.Rlong H ω y o = 0
  long_sum : ∀ H ω y, L.valid H ω y → X.g.low (X.p.J n) y.1 → ∑ o, rowAt L.ht.hp.Rlong H ω y o = 1
  long_support : ∀ H ω y o, rowAt L.ht.hp.Rlong H ω y o ≠ 0 → ∀ a ∈ evenNbrs y, ∀ c,
    X.evenRefOf (L.elig H) H ω a = some c → ∀ z ∈ X.refBlocks ω a c, X.BlockHits _ z o.2
  long_deletion : ∀ H ω y, L.valid H ω y → X.g.low (X.p.J n) y.1 →
    ∀ c ∈ X.refsOn H (X.actualRecord (L.elig H) H ω y) (arraysOf ω), ∀ o,
      rowAt L.ht.hp.Rlong H ω y o ≤ Real.exp (X.p.a 4 * X.refLen c.2.1 c.2.2) *
        X.step3PostOn H (X.actualRecord (L.elig H) H ω y) (arraysOf ω) (some c) (fun _ => o.2)
  long_local : ∀ H y, FinProb.DependsOn (fun ω => rowAt L.ht.hp.Rlong H ω y)
    (X.scopeBall (h := L.ht) y.1 (L.ht.hp.r + L.slack))
  /-- Disintegration of the target-averaged short-row mean (05:910–929,975–985). -/
  short_mean : ∀ b hi y lo x, X.g.low (X.p.J n) y.1 →
    ∑ y', (X.prior b (X.g.roleKey (X.p.J n) y.1)).w y' *
        (X.centreLaw L.ht (b, X.joinHidden hi (Function.update lo (X.lowIdxOf (X.g.roleKey (X.p.J n) y.1))
          (fun _ => y')))).expect (fun ω => (N : ℝ) * rowAt (L.ht.hp.Rshort (X.p.m n))
            (b, X.joinHidden hi (Function.update lo (X.lowIdxOf (X.g.roleKey (X.p.J n) y.1))
              (fun _ => y'))) ω y (0, x)) =
      (N : ℝ) * @Finset.sum (Data b hi y) ℝ _ (@Finset.univ _ (dataFintype b hi y)) (fun d =>
        (selExp b hi y lo).selectedMass d *
          (selExp b hi y lo).proxyRow (Real.exp (-(X.p.delta * X.p.kPrime n (X.g.severity y.1)))) d x)
  /-- Key locality of the short-row mean (05:991–1001). -/
  short_local : ∀ b hi y x, FinProb.DependsOn
    (fun lo => (X.centreLaw L.ht (b, X.joinHidden hi lo)).expect
      (fun ω => (N : ℝ) * rowAt (L.ht.hp.Rshort (X.p.m n)) (b, X.joinHidden hi lo) ω y (0, x)))
    (Finset.univ.filter fun k : X.LowIdx =>
      hammingDist k.2.1 (X.g.sign y.1) ≤ Cloc * Nat.sqrt (X.p.m n))

attribute [instance] LowTable5.dataFintype

end K

/-- SUB-LEMMA K1 (05:896–985): the short-rule selection table, its rows at every radius, their
pointwise properties (row comparison `≤ ε⁻¹ P`, Step 3 deletion multiplier `e^{a₄ k_c}`, cap
`e^{D_L}/N`), the disintegration identity and the key locality.  The table is built at fixed
`b, hi, lo` outside the target, as in TeX 05:898–903. -/
theorem lowTable_exists : ∀ (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) → ∀ Ckey : ℕ,
    ∃ Cloc : ℕ, ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
      X.p = p → (∀ x : CubeVertex n, ∀ ℓ ∈ X.g.typeKeys (X.p.J n) x, (X.g.key x).1 ∈ binList5 ℓ.coarse) →
        ∀ L : X.CentreLayer5, X.LowLayer5 L Ckey (cL p.pre1) (cH p.pre1) →
          Nonempty (LowTable5 X L Cloc) := by
  sorry

/-- SUB-LEMMA K2 (05:987–1001): at a good history the long-row mean exceeds the short-row mean
by at most `1`: rows agree when neighbouring choices agree (`rowAt_congr`), the height lemma
bounds mismatch by `o(e^{-2m^{1/5}})` at each of `O(n)` neighbours on correct sizes
(`LowLayer5.size_failure` for the rest), and the cap is `e^{D_L}`. -/
theorem lowTable_long_vs_short : ∀ (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) → ∀ Ckey : ℕ,
    ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
      X.p = p → ∀ L : X.CentreLayer5, X.LowLayer5 L Ckey (cL p.pre1) (cH p.pre1) →
        ∀ (Cloc : ℕ) (T : LowTable5 X L Cloc) (H : X.KeyHist), X.KeyGood5 H (cL p.pre1) (cH p.pre1) →
          ∀ y x, X.g.low (X.p.J n) y.1 →
            (X.centreLaw L.ht H).expect (fun ω => (N : ℝ) * T.rowAt L.ht.hp.Rlong H ω y (0, x)) ≤
              (X.centreLaw L.ht H).expect
                (fun ω => (N : ℝ) * T.rowAt (L.ht.hp.Rshort (X.p.m n)) H ω y (0, x)) + 1 := by
  sorry

theorem expect_nonneg' {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ P.expect f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (hf ω)

theorem expect_le_const {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (f : Ω → ℝ) (c : ℝ)
    (hf : ∀ ω, f ω ≤ c) : P.expect f ≤ c := by
  calc P.expect f = ∑ ω, P.w ω * f ω := rfl
    _ ≤ ∑ ω, P.w ω * c := Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hf ω) (P.nonneg ω)
    _ = c := by rw [← Finset.sum_mul, P.sum_eq_one, one_mul]

/-- The low rows from a selection table and the comparison. -/
def lowRowsOf (X : Setup5 γ K' χ n N E G) (L : X.CentreLayer5) (cL cH : ℝ) (Cloc : ℕ)
    (T : LowTable5 X L Cloc)
    (hcmp : ∀ H, X.KeyGood5 H cL cH → ∀ y x, X.g.low (X.p.J n) y.1 →
      (X.centreLaw L.ht H).expect (fun ω => (N : ℝ) * T.rowAt L.ht.hp.Rlong H ω y (0, x)) ≤
        (X.centreLaw L.ht H).expect
          (fun ω => (N : ℝ) * T.rowAt (L.ht.hp.Rshort (X.p.m n)) H ω y (0, x)) + 1) :
    X.LowRows5 L cL cH where
  row := T.rowAt L.ht.hp.Rlong
  proxy H y x := (X.centreLaw L.ht H).expect
    (fun ω => (N : ℝ) * T.rowAt (L.ht.hp.Rshort (X.p.m n)) H ω y (0, x))
  row_nonneg := T.rowAt_nonneg _
  row_high := T.rowAt_high _
  row_index := T.long_index
  row_invalid := T.long_invalid
  row_sum := T.long_sum
  row_cap := T.rowAt_cap _
  row_support := T.long_support
  row_deletion := T.long_deletion
  row_local := T.long_local
  long_vs_proxy := hcmp
  proxy_nonneg H y x := expect_nonneg' _ _ fun ω =>
    mul_nonneg (Nat.cast_nonneg _) (T.rowAt_nonneg _ H ω y _)
  proxy_high H y x hy := by
    simp [FinProb.expect, T.rowAt_high _ H _ y _ hy]
  proxy_cap H y x := expect_le_const _ _ _ fun ω => T.rowAt_cap _ H ω y _
  proxyRadius := Cloc
  proxy_local b hi y := by
    intro lo lo' h
    funext x
    exact T.short_local b hi y x lo lo' h
  Data := T.Data
  dataFintype := T.dataFintype
  selExp := T.selExp
  selExp_prior := T.selExp_prior
  selExp_records := T.selExp_records
  selExp_mean := T.short_mean

/-- L5.1k rows from the sub-lemmas. -/
theorem L5_1k_rows_proof : ∀ (cL cH : Pre15 → ℝ), (∀ x, 0 < cL x ∧ 0 < cH x) → ∀ Ckey : ℕ,
    ∃ Cloc : ℕ, ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G),
      X.p = p → (∀ x : CubeVertex n, ∀ ℓ ∈ X.g.typeKeys (X.p.J n) x, (X.g.key x).1 ∈ binList5 ℓ.coarse) →
        ∀ L : X.CentreLayer5, X.LowLayer5 L Ckey (cL p.pre1) (cH p.pre1) →
          ∃ LR : X.LowRows5 L (cL p.pre1) (cH p.pre1), LR.proxyRadius ≤ Cloc := by
  intro cL cH hc Ckey
  obtain ⟨Cloc, R₁, h₁⟩ := lowTable_exists (γ := γ) (K' := K') (χ := χ) cL cH hc Ckey
  obtain ⟨R₂, h₂⟩ := lowTable_long_vs_short (γ := γ) (K' := K') (χ := χ) cL cH hc Ckey
  refine ⟨Cloc, R₁.join R₂, fun p hp => ?_⟩
  obtain ⟨hp₁, hp₂⟩ := ParamReq5.holds_of_join hp
  obtain ⟨n₁, hn₁⟩ := h₁ p hp₁
  obtain ⟨n₂, hn₂⟩ := h₂ p hp₂
  refine ⟨max n₁ n₂, fun n hn N E G X hXp hcov L hL => ?_⟩
  obtain ⟨T⟩ := hn₁ n (le_trans (le_max_left _ _) hn) N E G X hXp hcov L hL
  exact ⟨lowRowsOf X L _ _ Cloc T (hn₂ n (le_trans (le_max_right _ _) hn) N E G X hXp L hL Cloc T),
    le_rfl⟩

/-- The assembled proofs have exactly the frozen target types. -/
theorem L5_1j_matches : type_of% @Setup5.L5_1j := @L5_1j_proof
theorem L5_1k_rows_matches : type_of% @Setup5.L5_1k_rows := @L5_1k_rows_proof

end

end HypercubeRamsey.Setup5.Lane_opus_s05
