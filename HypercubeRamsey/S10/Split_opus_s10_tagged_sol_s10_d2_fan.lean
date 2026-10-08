import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2

/-! Own-fan bounds with selector agreement required only on queried sites. -/

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

private theorem p10_1k_ownTupleId_selection_spec {n m : ℕ} (δ : ℝ)
    (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (Sites : (p10_1kHeightParams n m δ).Sites)
    (P A : (p10_1kHeightParams n m δ).Loc → Bool)
    (E : (p10_1kHeightParams n m δ).EligMap)
    (τ : (p10_1kHeightParams n m δ).Ties)
    (hlegal : (p10_1kHeightParams n m δ).Legal P E Sites)
    (hmatch : ∀ v ∈ Sites, selected (q.1, v) =
      (p10_1kHeightParams n m δ).selection Sites P A E τ v)
    (hinSites : ∀ v ℓ, selected (q.1, v) = some ℓ → v ∈ Sites)
    (id : P10_1kProspectiveId n m δ)
    (hid : id ∈ p10_1kOddGroupOwnTupleIds δ q selected) :
    ∃ v loc j, v ∈ Sites ∧ (q.1, v) ∈ p10_1kProjectedNeighborEnvelope q ∧
      selected (q.1, v) = some loc ∧ id = (q.1, loc) ∧
      (p10_1kHeightParams n m δ).height Sites P A E
        (p10_1kHeightParams n m δ).Rlong v = j.val ∧
      j.val < (p10_1kHeightParams n m δ).H ∧
      ¬ (p10_1kHeightParams n m δ).Bad P A E v j ∧
      loc ∈ E v j ∧ A loc = true ∧ P loc = true ∧
      loc.2 = j ∧ _root_.hammingDist loc.1 v ≤ (p10_1kHeightParams n m δ).r := by
  obtain ⟨site, loc, henv, hslice, hselected, hidEq⟩ :=
    p10_1k_ownTupleId_source δ q selected id hid
  have hsiteEq : (q.1, site.2) = site := Prod.ext hslice.symm rfl
  have henv' : (q.1, site.2) ∈ p10_1kProjectedNeighborEnvelope q := by
    rw [hsiteEq]
    exact henv
  have hselected' : selected (q.1, site.2) = some loc := by
    exact (congrArg selected hsiteEq).trans hselected
  have hv : site.2 ∈ Sites := hinSites site.2 loc hselected'
  have hselect : (p10_1kHeightParams n m δ).selection Sites P A E τ site.2 =
      some loc := by
    rw [← hmatch site.2 hv]
    exact hselected'
  obtain ⟨j, hheight, hj, hbad, hE, hA, hP, hlevel, hdist⟩ :=
    p10_1k_selection_legal_spec_of_some Sites P A E τ hlegal
      site.2 hv loc hselect
  have hidEq' : id = (q.1, loc) := by
    calc
      id = (site.1, loc) := hidEq
      _ = (q.1, loc) := by rw [hslice]
  exact ⟨site.2, loc, j, hv, henv', hselected', hidEq', hheight, hj, hbad,
    hE, hA, hP, hlevel, hdist⟩

/-- A finite set whose level map has at most `L` values and at most `M`
members per level has size at most `L * M`. -/
private theorem p10_1k_card_le_levels_mul {α β : Type*} [DecidableEq β]
    (S : Finset α) (level : α → β) (levels : Finset β) (L M : ℕ)
    (hcover : ∀ a ∈ S, level a ∈ levels)
    (hlevels : levels.card ≤ L)
    (hfiber : ∀ b ∈ levels, (S.filter fun a => level a = b).card ≤ M) :
    S.card ≤ L * M := by
  have hsum : S.card =
      ∑ b ∈ levels, (S.filter fun a => level a = b).card := by
    simpa using Finset.card_eq_sum_card_fiberwise hcover
  calc
    S.card = ∑ b ∈ levels, (S.filter fun a => level a = b).card := hsum
    _ ≤ ∑ b ∈ levels, M := by
      apply Finset.sum_le_sum
      intro b hb
      exact hfiber b hb
    _ = levels.card * M := by simp
    _ ≤ L * M := Nat.mul_le_mul_right M hlevels

/-- Under GoodHeights, selected IDs in one own-slice group occupy at most
three height levels. -/
theorem p10_1kOddGroupOwnTupleIds_level_image_card_le_three
    {n m : ℕ} (δ : ℝ) (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (Sites : (p10_1kHeightParams n m δ).Sites)
    (P A : (p10_1kHeightParams n m δ).Loc → Bool)
    (E : (p10_1kHeightParams n m δ).EligMap)
    (τ : (p10_1kHeightParams n m δ).Ties)
    (hlegal : (p10_1kHeightParams n m δ).Legal P E Sites)
    (hgood : (p10_1kHeightParams n m δ).GoodHeights Sites P A E)
    (hmatch : ∀ v ∈ Sites, selected (q.1, v) =
      (p10_1kHeightParams n m δ).selection Sites P A E τ v)
    (hinSites : ∀ v ℓ, selected (q.1, v) = some ℓ → v ∈ Sites) :
    ((p10_1kOddGroupOwnTupleIds δ q selected).image
      (fun id => id.2.2.val)).card ≤ 3 := by
  classical
  let p := p10_1kHeightParams n m δ
  let Own := p10_1kOddGroupOwnTupleIds δ q selected
  let level : P10_1kProspectiveId n m δ → ℕ := fun id => id.2.2.val
  by_cases hnon : Own.Nonempty
  · obtain ⟨id₀, hid₀⟩ := hnon
    obtain ⟨v₀, loc₀, j₀, hv₀, henv₀, hsel₀, hid₀eq, hheight₀,
      hj₀, hbad₀, hE₀, hA₀, hP₀, hlevel₀, hdist₀⟩ :=
      p10_1k_ownTupleId_selection_spec δ q selected Sites P A E τ
        hlegal hmatch hinSites id₀ hid₀
    have hsiteQ₀ : _root_.hammingDist q.2 v₀ ≤ 3 :=
      p10_1k_envelope_same_slice_residual_dist_le_three q (q.1, v₀) henv₀ rfl
    have hbaseHeight : p.height Sites P A E p.Rlong v₀ = level id₀ := by
      calc
        p.height Sites P A E p.Rlong v₀ = j₀.val := hheight₀
        _ = loc₀.2.val := congrArg Fin.val hlevel₀.symm
        _ = level id₀ := by dsimp [level]; rw [hid₀eq]
    let base := level id₀
    let interval := Finset.Icc (base - 1) (base + 1)
    have hlevelWithin (id : P10_1kProspectiveId n m δ)
        (hid : id ∈ Own) : level id ∈ interval := by
      obtain ⟨v, loc, j, hv, henv, hsel, hideq, hheight, hj, hbad,
        hE, hA, hP, hlevel, hdist⟩ :=
        p10_1k_ownTupleId_selection_spec δ q selected Sites P A E τ
          hlegal hmatch hinSites id hid
      have hsiteQ : _root_.hammingDist q.2 v ≤ 3 :=
        p10_1k_envelope_same_slice_residual_dist_le_three q (q.1, v) henv rfl
      let qres : CubeVertex (n - m) := q.2
      have hsiteQ₀' : _root_.hammingDist v₀ qres ≤ 3 := by
        change _root_.hammingDist v₀ q.2 ≤ 3
        exact p10_1k_envelope_same_slice_residual_dist_le_three_symm
          q (q.1, v₀) henv₀ rfl
      have hsiteQ' : _root_.hammingDist qres v ≤ 3 := by
        change _root_.hammingDist q.2 v ≤ 3
        exact hsiteQ
      have hsiteV : _root_.hammingDist v₀ v ≤ p.D := by
        have hsiteV₆ : _root_.hammingDist v₀ v ≤ 6 := by
          calc
            _root_.hammingDist v₀ v ≤ _root_.hammingDist v₀ qres + _root_.hammingDist qres v :=
              hammingDist_triangle v₀ qres v
            _ ≤ 3 + 3 := add_le_add hsiteQ₀' hsiteQ'
            _ = 6 := by norm_num
        simpa [p, p10_1kHeightParams] using hsiteV₆
      have hvariation := (hgood v₀ hv₀).2.2 v hv hsiteV
      have hbaseLevel : level id₀ = loc₀.2.val := by
        dsimp [level]
        rw [hid₀eq]
      have hlevelId : level id = loc.2.val := by
        dsimp [level]
        rw [hideq]
      have hvariation' :
          |(level id₀ : ℤ) - (level id : ℤ)| ≤ 1 := by
        rw [hbaseHeight, hheight, ← hlevel] at hvariation
        simpa [hbaseLevel, hlevelId] using hvariation
      have hBounds := abs_le.mp hvariation'
      apply Finset.mem_Icc.mpr
      constructor <;> dsimp [base] <;> omega
    have hlevelsSubset :
        (Own.image level) ⊆ interval := by
      intro j hj
      obtain ⟨id, hid, rfl⟩ := Finset.mem_image.mp hj
      exact hlevelWithin id hid
    have hintervalCard : interval.card ≤ 3 := by
      dsimp [interval]
      simp only [Nat.card_Icc]
      omega
    calc
      (Own.image level).card ≤ interval.card := Finset.card_le_card hlevelsSubset
      _ ≤ 3 := hintervalCard
  · have hempty : Own = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
    simp [Own, hempty]

private theorem p10_1k_cube_hammingDist_comm {d : ℕ}
    (u v : CubeVertex d) : _root_.hammingDist u v = _root_.hammingDist v u := by
  exact _root_.hammingDist_comm u v

/-- At a fixed selected height, the own-slice IDs inject into the nonbad
crowd around one selected site. -/
theorem p10_1kOddGroupOwnTupleIds_height_fiber_mass_bound
    {n m : ℕ} (δ : ℝ) (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (Sites : (p10_1kHeightParams n m δ).Sites)
    (P A : (p10_1kHeightParams n m δ).Loc → Bool)
    (E : (p10_1kHeightParams n m δ).EligMap)
    (τ : (p10_1kHeightParams n m δ).Ties)
    (hlegal : (p10_1kHeightParams n m δ).Legal P E Sites)
    (hgood : (p10_1kHeightParams n m δ).GoodHeights Sites P A E)
    (hmatch : ∀ v ∈ Sites, selected (q.1, v) =
      (p10_1kHeightParams n m δ).selection Sites P A E τ v)
    (hinSites : ∀ v ℓ, selected (q.1, v) = some ℓ → v ∈ Sites)
    (b : ℕ)
    (hfiber : ∃ id ∈ p10_1kOddGroupOwnTupleIds δ q selected,
      id.2.2.val = b) :
    (((p10_1kOddGroupOwnTupleIds δ q selected).filter
      (fun id => id.2.2.val = b)).card : ℝ) ≤
        (n : ℝ) ^ (p10_1kHeightParams n m δ).b := by
  classical
  let p := p10_1kHeightParams n m δ
  let Own := p10_1kOddGroupOwnTupleIds δ q selected
  let Fiber := Own.filter (fun id => id.2.2.val = b)
  obtain ⟨id₀, hid₀, hlevel₀⟩ := hfiber
  obtain ⟨v₀, loc₀, j₀, hv₀, henv₀, hsel₀, hid₀eq, hheight₀,
    hj₀, hbad₀, hE₀, hA₀, hP₀, hlocLevel₀, hdist₀⟩ :=
    p10_1k_ownTupleId_selection_spec δ q selected Sites P A E τ
      hlegal hmatch hinSites id₀ hid₀
  let level : P10_1kProspectiveId n m δ → ℕ := fun id => id.2.2.val
  have hlevelId₀ : level id₀ = loc₀.2.val := by
    dsimp [level]
    rw [hid₀eq]
  have hj₀b : j₀.val = b := by
    calc
      j₀.val = loc₀.2.val := congrArg Fin.val hlocLevel₀.symm
      _ = level id₀ := hlevelId₀.symm
      _ = b := hlevel₀
  have hheightB : p.height Sites P A E p.Rlong v₀ = b :=
    hheight₀.trans hj₀b
  have hgood₀ := hgood v₀ hv₀
  have hbH : b < p.H := by
    rw [← hheightB]
    exact hgood₀.1
  let j : Fin (p.H + 1) := ⟨b, by omega⟩
  have hnoBadN : ¬ p.BadN P A E v₀ b := by
    rw [← hheightB]
    exact hgood₀.2.1
  have hnotBad₀ : ¬ p.Bad P A E v₀ j := by
    intro hbad
    apply hnoBadN
    refine ⟨by omega, ?_⟩
    simpa [j] using hbad
  let qres : CubeVertex p.d := q.2
  have hq₀ : _root_.hammingDist v₀ qres ≤ 3 := by
    change _root_.hammingDist v₀ q.2 ≤ 3
    exact p10_1k_envelope_same_slice_residual_dist_le_three_symm
      q (q.1, v₀) henv₀ rfl
  let crowd : Finset (CubeVertex p.d) :=
    Finset.univ.filter fun u =>
      P (u, j) = true ∧ A (u, j) = true ∧
        _root_.hammingDist u v₀ ≤ p.r + p.D
  have hnotCrowded : ¬ (p.n : ℝ) ^ p.b < (crowd.card : ℝ) := by
    intro hlarge
    apply hnotBad₀
    right
    simpa [HDParams.Bad, crowd] using hlarge
  have hcrowd : (crowd.card : ℝ) ≤ (p.n : ℝ) ^ p.b := le_of_not_gt hnotCrowded
  have hmap : Set.MapsTo (fun id : P10_1kProspectiveId n m δ => id.2.1)
      (Fiber : Set (P10_1kProspectiveId n m δ)) (crowd : Set (CubeVertex p.d)) := by
    intro id hid
    have hparts := Finset.mem_filter.mp hid
    have hown : id ∈ Own := hparts.1
    obtain ⟨v, loc, j', hv, henv, hsel, hideq, hheight, hj', hbad,
      hE, hA, hP, hlocLevel, hdist⟩ :=
      p10_1k_ownTupleId_selection_spec δ q selected Sites P A E τ
        hlegal hmatch hinSites id hown
    have hlevelId : level id = loc.2.val := by
      dsimp [level]
      rw [hideq]
    have hlocVal : loc.2.val = b := hlevelId.symm.trans hparts.2
    have hlocEq : loc.2 = j := Fin.ext hlocVal
    have hq : _root_.hammingDist qres v ≤ 3 := by
      change _root_.hammingDist q.2 v ≤ 3
      exact p10_1k_envelope_same_slice_residual_dist_le_three
        q (q.1, v) henv rfl
    have hbaseDist : _root_.hammingDist v v₀ ≤ p.D := by
      -- The reverse envelope bound for `v₀` and the forward bound for `v`
      -- place both sites within three residual steps of `q`.
      have hqv₀ : _root_.hammingDist qres v₀ ≤ 3 := by
        rw [p10_1k_cube_hammingDist_comm]
        exact hq₀
      have hvq : _root_.hammingDist v qres ≤ 3 := by
        rw [p10_1k_cube_hammingDist_comm]
        exact hq
      have hdistV : _root_.hammingDist v v₀ ≤ 6 := by
        calc
          _root_.hammingDist v v₀ ≤ _root_.hammingDist v qres + _root_.hammingDist qres v₀ :=
            hammingDist_triangle v qres v₀
          _ ≤ 3 + 3 := add_le_add hvq hqv₀
          _ = 6 := by norm_num
      simpa [p, p10_1kHeightParams] using hdistV
    have hcenter : _root_.hammingDist loc.1 v₀ ≤ p.r + p.D := by
      calc
        _root_.hammingDist loc.1 v₀ ≤ _root_.hammingDist loc.1 v + _root_.hammingDist v v₀ :=
          hammingDist_triangle loc.1 v v₀
        _ ≤ p.r + p.D := add_le_add hdist hbaseDist
    have hPj : P (loc.1, j) = true := by
      rw [← hlocEq]
      exact hP
    have hAj : A (loc.1, j) = true := by
      rw [← hlocEq]
      exact hA
    have hcenterMap : _root_.hammingDist id.2.1 v₀ ≤ p.r + p.D := by
      rw [hideq]
      exact hcenter
    have hPmap : P (id.2.1, j) = true := by
      rw [hideq]
      exact hPj
    have hAmap : A (id.2.1, j) = true := by
      rw [hideq]
      exact hAj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hPmap, hAmap, hcenterMap⟩
  have hinj : (Fiber : Set (P10_1kProspectiveId n m δ)).InjOn
      (fun id => id.2.1) := by
    intro id₁ h₁ id₂ h₂ hcenters
    have hparts₁ := Finset.mem_filter.mp h₁
    have hparts₂ := Finset.mem_filter.mp h₂
    have hslice₁ : id₁.1 = q.1 := by
      have hown := Finset.mem_filter.mp hparts₁.1
      exact hown.2
    have hslice₂ : id₂.1 = q.1 := by
      have hown := Finset.mem_filter.mp hparts₂.1
      exact hown.2
    have hfin₁ : id₁.2.2.val = b := hparts₁.2
    have hfin₂ : id₂.2.2.val = b := hparts₂.2
    apply Prod.ext
    · exact hslice₁.trans hslice₂.symm
    · apply Prod.ext
      · exact hcenters
      · exact Fin.ext (hfin₁.trans hfin₂.symm)
  have hcard := Finset.card_le_card_of_injOn
    (fun id : P10_1kProspectiveId n m δ => id.2.1) hmap hinj
  have hcardReal : (Fiber.card : ℝ) ≤ (crowd.card : ℝ) := by
    exact_mod_cast hcard
  calc
    (Fiber.card : ℝ) ≤ (crowd.card : ℝ) := hcardReal
    _ ≤ (p.n : ℝ) ^ p.b := hcrowd
    _ = (n : ℝ) ^ (p10_1kHeightParams n m δ).b := by rfl

/-- The selected own-slice IDs have at most three height fibers, each bounded
by the nonbad crowd threshold. -/
theorem p10_1kOddGroupOwnTupleIds_card_le_three_mul_ceil
    {n m : ℕ} (δ : ℝ) (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (Sites : (p10_1kHeightParams n m δ).Sites)
    (P A : (p10_1kHeightParams n m δ).Loc → Bool)
    (E : (p10_1kHeightParams n m δ).EligMap)
    (τ : (p10_1kHeightParams n m δ).Ties)
    (hlegal : (p10_1kHeightParams n m δ).Legal P E Sites)
    (hgood : (p10_1kHeightParams n m δ).GoodHeights Sites P A E)
    (hmatch : ∀ v ∈ Sites, selected (q.1, v) =
      (p10_1kHeightParams n m δ).selection Sites P A E τ v)
    (hinSites : ∀ v ℓ, selected (q.1, v) = some ℓ → v ∈ Sites) :
    (p10_1kOddGroupOwnTupleIds δ q selected).card ≤
      3 * Nat.ceil ((n : ℝ) ^ (p10_1kHeightParams n m δ).b) := by
  classical
  let p := p10_1kHeightParams n m δ
  let Own := p10_1kOddGroupOwnTupleIds δ q selected
  let level : P10_1kProspectiveId n m δ → ℕ := fun id => id.2.2.val
  let T : ℕ := Nat.ceil ((n : ℝ) ^ p.b)
  have hlevels : (Own.image level).card ≤ 3 := by
    simpa [Own, level] using
      p10_1kOddGroupOwnTupleIds_level_image_card_le_three
        δ q selected Sites P A E τ hlegal hgood hmatch hinSites
  apply p10_1k_card_le_levels_mul Own level (Own.image level) 3 T
  · intro id hid
    exact Finset.mem_image.mpr ⟨id, hid, rfl⟩
  · exact hlevels
  · intro b hb
    obtain ⟨id, hid, hlevel⟩ := Finset.mem_image.mp hb
    have hmass := p10_1kOddGroupOwnTupleIds_height_fiber_mass_bound
      δ q selected Sites P A E τ hlegal hgood hmatch hinSites b ⟨id, hid, hlevel⟩
    have hmass' : ((Own.filter (fun id => level id = b)).card : ℝ) ≤
        (n : ℝ) ^ p.b := by
      simpa [Own, level] using hmass
    have hceil : (n : ℝ) ^ p.b ≤ (T : ℝ) := by
      dsimp [T]
      exact Nat.le_ceil _
    have hreal : ((Own.filter (fun id => level id = b)).card : ℝ) ≤
        (T : ℝ) := hmass'.trans hceil
    exact_mod_cast hreal

/-- Once the exponent gap absorbs the rounding constants, the own-slice
fan is bounded by the height-count scale used by P10.1c. -/
theorem own_fan_card_le
    {n m : ℕ} (δ : ℝ) (q : P10_1kProjectedSite n m)
    (selected : P10_1kProjectedSite n m →
      Option (p10_1kHeightParams n m δ).Loc)
    (Sites : (p10_1kHeightParams n m δ).Sites)
    (P A : (p10_1kHeightParams n m δ).Loc → Bool)
    (E : (p10_1kHeightParams n m δ).EligMap)
    (τ : (p10_1kHeightParams n m δ).Ties)
    (hlegal : (p10_1kHeightParams n m δ).Legal P E Sites)
    (hgood : (p10_1kHeightParams n m δ).GoodHeights Sites P A E)
    (hmatch : ∀ v ∈ Sites, selected (q.1, v) =
      (p10_1kHeightParams n m δ).selection Sites P A E τ v)
    (hinSites : ∀ v ℓ, selected (q.1, v) = some ℓ → v ∈ Sites)
    (hn : 2 ≤ n) (hδ : 0 < δ)
    (hgap : 6 * (n : ℝ) ^ (140 * δ) < (n : ℝ) ^ (141 * δ)) :
    (p10_1kOddGroupOwnTupleIds δ q selected).card ≤
      p10_1kHeightCount n δ := by
  classical
  let x : ℝ := (n : ℝ) ^ (140 * δ)
  let y : ℝ := (n : ℝ) ^ (141 * δ)
  have hxone : 1 ≤ x := by
    dsimp [x]
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    calc
      1 = (n : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero]
      _ ≤ (n : ℝ) ^ (140 * δ) :=
        Real.rpow_le_rpow_of_exponent_le hnreal (by positivity)
  have hceilX : (Nat.ceil x : ℝ) ≤ x + 1 := by
    have hceilNat : Nat.ceil x ≤ Nat.floor x + 1 := Nat.ceil_le_floor_add_one x
    have hcast : (Nat.ceil x : ℝ) ≤ (Nat.floor x : ℝ) + 1 := by
      exact_mod_cast hceilNat
    have hfloor := Nat.floor_le (by positivity : 0 ≤ x)
    linarith
  have hrounded : ((3 * Nat.ceil x : ℕ) : ℝ) ≤ y := by
    calc
      ((3 * Nat.ceil x : ℕ) : ℝ) = 3 * (Nat.ceil x : ℝ) := by norm_num
      _ ≤ 3 * (x + 1) := by gcongr
      _ ≤ 6 * x := by nlinarith [hxone]
      _ ≤ y := le_of_lt (by simpa [x, y] using hgap)
  have hyceil : y ≤ (Nat.ceil y : ℝ) := Nat.le_ceil y
  have hnat : 3 * Nat.ceil x ≤ Nat.ceil y := by
    exact_mod_cast hrounded.trans hyceil
  have hfan := p10_1kOddGroupOwnTupleIds_card_le_three_mul_ceil
    δ q selected Sites P A E τ hlegal hgood hmatch hinSites
  have hfan' : (p10_1kOddGroupOwnTupleIds δ q selected).card ≤
      3 * Nat.ceil x := by
    simpa [x, p10_1kHeightParams] using hfan
  simpa [y, p10_1kHeightCount] using hfan'.trans hnat


end HypercubeRamsey.Lane_sol_s10_d2
