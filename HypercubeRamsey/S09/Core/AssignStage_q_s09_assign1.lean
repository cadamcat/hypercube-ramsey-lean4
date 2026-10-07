import HypercubeRamsey.Framework.FinProb
import HypercubeRamsey.S09.Core.Scales
import HypercubeRamsey.S09.Core.Experiment

namespace HypercubeRamsey.Lane_q_s09_assign1

open Filter
open OAI.HypercubeRamsey
open scoped BigOperators

/-- Split a dependent product into one coordinate and all remaining coordinates. -/
def coordSplitEquiv {ι : Type*} [DecidableEq ι] {Ω : ι → Type*} (j : ι) :
    (∀ i, Ω i) ≃ Ω j × (∀ i : {i // i ≠ j}, Ω i.1) where
  toFun ω := (ω j, fun i => ω i.1)
  invFun p i := if h : i = j then h ▸ p.1 else p.2 ⟨i, h⟩
  left_inv ω := by
    funext i
    by_cases h : i = j
    · subst i
      simp
    · simp [h]
  right_inv p := by
    rcases p with ⟨x, τ⟩
    apply Prod.ext
    · simp
    · funext i
      simp [i.2]

/-- Integrate a finite product law by first summing one selected coordinate. -/
theorem pi_expect_split_coord {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (j : ι) (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ x, (P j).w x *
        (FinProb.pi (fun i : {i // i ≠ j} => P i.1)).expect
          (fun τ => f ((coordSplitEquiv j).symm (x, τ))) := by
  classical
  let e : (∀ i, Ω i) ≃ Ω j × (∀ i : {i // i ≠ j}, Ω i.1) := coordSplitEquiv j
  have hweight (x : Ω j) (τ : ∀ i : {i // i ≠ j}, Ω i.1) :
      (∏ i, (P i).w ((e.symm (x, τ)) i)) =
        (P j).w x * ∏ i : {i // i ≠ j}, (P i.1).w (τ i) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne
      (fun i => (P i).w ((e.symm (x, τ)) i)) j]
    have hj : (e.symm (x, τ)) j = x := by simp [e, coordSplitEquiv]
    rw [hj]
    congr 1
    apply Fintype.prod_congr
    intro i
    have hi : (e.symm (x, τ)) i.1 = τ i := by
      simp [e, coordSplitEquiv, i.2]
    rw [hi]
  simp only [FinProb.expect, FinProb.pi]
  change (∑ ω, (∏ i, (P i).w (ω i)) * f ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ τ, (∏ i, (P i).w ((e.symm (x, τ)) i)) * f (e.symm (x, τ))) =
        ∑ τ, (P j).w x * (∏ i : {i // i ≠ j}, (P i.1).w (τ i)) *
          f (e.symm (x, τ)) := by
            apply Finset.sum_congr rfl
            intro τ hτ
            rw [hweight]
    _ = (P j).w x *
        ∑ τ, (∏ i : {i // i ≠ j}, (P i.1).w (τ i)) * f (e.symm (x, τ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro τ hτ
          ring

/-- Monotonicity of event probabilities on a finite law. -/
theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A B : Ω → Prop)
    (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB, P.nonneg ω]
  · by_cases hB : B ω
    · simp [hA, hB, P.nonneg ω]
    · simp [hA, hB]

/-- The logarithm of the dependency-degree base is little-oh of `n^u` when the radius exponent is below `u`. -/
theorem degreeLogSmall9 (P : Params9) (hexps : ScaleExps9 P) {c : ℝ} (hc : 0 < c) :
    ∃ n₀, ∀ n ≥ n₀,
      (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
        (c / 4) * (n : ℝ) ^ P.u := by
  rcases hexps with ⟨heps, hepsσ, hu, hσu, _⟩
  have hσ : 0 < (P.σ : ℝ) := lt_trans heps hepsσ
  let δ : ℝ := (P.u - P.σ) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδu : δ < P.u := by dsimp [δ]; linarith [hσ]
  let C : ℝ := (2 : ℝ) ^ δ / δ
  have hC : 0 < C := by dsimp [C]; positivity
  have hneg1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-δ)) atTop (nhds 0) := by
    exact (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hneg2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (δ - P.u)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hδu)).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, neg_sub] using h
  let ratio : ℕ → ℝ := fun n => 2 * C * (n : ℝ) ^ (-δ) + 8 * C * (n : ℝ) ^ (δ - P.u)
  have hratio : Tendsto ratio atTop (nhds 0) := by
    dsimp [ratio]
    simpa using (hneg1.const_mul (2 * C)).add (hneg2.const_mul (8 * C))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (hratio.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < c / 4)))
  refine ⟨max n₀ 1, ?_⟩
  intro n hn
  have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hrad : (P.radius n : ℝ) ≤ (n : ℝ) ^ (P.σ : ℝ) := by
    dsimp [Params9.radius]
    exact Nat.floor_le (by positivity : 0 ≤ (n : ℝ) ^ (P.σ : ℝ))
  have hR : 2 * (P.radius n : ℝ) + 8 ≤ 2 * (n : ℝ) ^ (P.σ : ℝ) + 8 := by nlinarith [hrad]
  have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) := by
    apply Real.log_nonneg
    linarith
  have hlog := Real.log_le_rpow_div (by positivity : 0 ≤ (n : ℝ) + 1) hδ
  have hnplus : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith [hnR1]
  have hpow : ((n : ℝ) + 1) ^ δ ≤ (2 : ℝ) ^ δ * (n : ℝ) ^ δ := by
    calc
      ((n : ℝ) + 1) ^ δ ≤ (2 * (n : ℝ)) ^ δ := Real.rpow_le_rpow (by positivity) hnplus hδ.le
      _ = (2 : ℝ) ^ δ * (n : ℝ) ^ δ := by
        rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hnR.le]
  have hnum :
      (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
        2 * C * (n : ℝ) ^ ((P.σ : ℝ) + δ) + 8 * C * (n : ℝ) ^ δ := by
    calc
      (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
          (2 * (n : ℝ) ^ (P.σ : ℝ) + 8) * Real.log ((n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hR hlog0
      _ ≤ (2 * (n : ℝ) ^ (P.σ : ℝ) + 8) * (((n : ℝ) + 1) ^ δ / δ) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (2 * (n : ℝ) ^ (P.σ : ℝ) + 8) * ((2 : ℝ) ^ δ * (n : ℝ) ^ δ / δ) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow hδ.le) (by positivity)
      _ = 2 * C * (n : ℝ) ^ ((P.σ : ℝ) + δ) + 8 * C * (n : ℝ) ^ δ := by
            dsimp [C]
            rw [Real.rpow_add hnR (P.σ : ℝ) δ]
            ring
  have hpowA : (n : ℝ) ^ ((P.σ : ℝ) + δ) = (n : ℝ) ^ P.u * (n : ℝ) ^ (-δ) := by
    rw [← Real.rpow_add hnR P.u (-δ)]
    congr 1
    dsimp [δ]
    ring
  have hpowB : (n : ℝ) ^ δ = (n : ℝ) ^ P.u * (n : ℝ) ^ (δ - P.u) := by
    rw [← Real.rpow_add hnR P.u (δ - P.u)]
    congr 1
    ring
  have hsmall : ratio n < c / 4 := hn₀ n hn₀'
  have hnum' : (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
      (n : ℝ) ^ P.u * ratio n := by
    calc
      (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
          2 * C * (n : ℝ) ^ ((P.σ : ℝ) + δ) + 8 * C * (n : ℝ) ^ δ := hnum
      _ = (n : ℝ) ^ P.u * ratio n := by
        rw [hpowA, hpowB]
        dsimp [ratio]
        ring
  calc
    (2 * (P.radius n : ℝ) + 8) * Real.log ((n : ℝ) + 1) ≤
        (n : ℝ) ^ P.u * ratio n := hnum'
    _ ≤ (c / 4) * (n : ℝ) ^ P.u := by
      calc
        (n : ℝ) ^ P.u * ratio n ≤ (n : ℝ) ^ P.u * (c / 4) :=
          mul_le_mul_of_nonneg_left (le_of_lt hsmall) (by positivity)
        _ = (c / 4) * (n : ℝ) ^ P.u := by ring

/-- A star scope contains every anchor read by each of its neighbouring odd rows. -/
theorem starScopeAnchorEq9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) :
    ∀ b : OddSites9 n, (cube n).Adj v.1 b.1 →
      ∀ c ∈ I.seen b.1, anc9 ω c = anc9 ω' c := by
  classical
  intro b hb c hc
  have hmem : Sum.inl c ∈ starScope9 I v := by
    unfold starScope9
    apply Finset.mem_biUnion.mpr
    refine ⟨b, ?_, ?_⟩
    · simp [hb]
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  simpa [anc9, Val9] using hω (Sum.inl c) hmem

/-- A star scope contains the mask coordinate of every neighbouring odd row. -/
theorem starScopeMaskEq9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i)
    (b : OddSites9 n) (hb : (cube n).Adj v.1 b.1) : msk9 ω b = msk9 ω' b := by
  have hmem : Sum.inr b ∈ starScope9 I v := by
    classical
    unfold starScope9
    apply Finset.mem_biUnion.mpr
    refine ⟨b, ?_, ?_⟩
    · simp [hb]
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  simpa [msk9, Val9] using hω (Sum.inr b) hmem

/-- The hit filter is unchanged when all anchors in its ID set agree. -/
theorem hitSetEqOfAnchors9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) (ω ω' : Outcome9 I N)
    (ids : Finset I.ID) (hids : ∀ c ∈ ids, anc9 ω c = anc9 ω' c) :
    hitSet9 E G ω ids = hitSet9 E G ω' ids := by
  classical
  ext y
  simp only [hitSet9, Finset.mem_filter, Finset.mem_univ, true_and]
  apply forall_congr'
  intro c
  apply forall_congr'
  intro hc
  rw [hids c hc]

/-- The local row and deletion laws are fixed by the coordinates in a star scope. -/
theorem starScopeRowsEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i)
    (b : OddSites9 n) (hb : (cube n).Adj v.1 b.1) :
    rowLaw9 S E G ω b = rowLaw9 S E G ω' b ∧
      ∀ t, delLaw9 S E G ω b t = delLaw9 S E G ω' b t := by
  classical
  have hanc := starScopeAnchorEq9 ω ω' hω b hb
  have hmask := starScopeMaskEq9 ω ω' hω b hb
  have hhit : hitSet9 E G ω (I.seen b.1) = hitSet9 E G ω' (I.seen b.1) :=
    hitSetEqOfAnchors9 E G ω ω' (I.seen b.1) hanc
  have hmasked : maskedLaw9 S ω b = maskedLaw9 S ω' b := by
    simp [maskedLaw9, hmask]
  constructor
  · simp [rowLaw9, hmasked, hhit]
  · intro t
    have hdelhit :
        hitSet9 E G ω ((I.seen b.1).erase t) =
          hitSet9 E G ω' ((I.seen b.1).erase t) :=
      hitSetEqOfAnchors9 E G ω ω' _ (fun c hc => hanc c (Finset.mem_of_mem_erase hc))
    simp [delLaw9, hmasked, hdelhit]

/-- The center ID of an even site is seen at every adjacent odd site. -/
theorem centerSeen9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {b : OddSites9 n} (hb : (cube n).Adj v.1 b.1) :
    I.center v.1 ∈ I.seen b.1 := by
  classical
  unfold IDMap9.seen seenIDs9
  apply Finset.mem_image.mpr
  refine ⟨v.1, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.symm⟩

/-- Every ID in a star row's full order is among that row's seen IDs. -/
theorem fullOrderMemSeen9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {b : OddSites9 n} (hb : (cube n).Adj v.1 b.1)
    {c : I.ID} (hc : c ∈ fullOrder9 I v b) : c ∈ I.seen b.1 := by
  classical
  unfold fullOrder9 at hc
  rcases List.mem_append.mp hc with houtercore | hlast
  · rcases List.mem_append.mp houtercore with houter | hcore
    · have hmem : c ∈ outerIDs9 I v b := by simpa using houter
      exact (Finset.mem_sdiff.mp hmem).1
    · have hmem : c ∈ coreIDs9 I v b := by simpa using hcore
      exact (Finset.mem_inter.mp (Finset.mem_erase.mp hmem).2).1
  · have hcenter : c = I.center v.1 := List.mem_singleton.mp hlast
    rw [hcenter]
    exact centerSeen9 hb

/-- Every ID in a star row's core order is among that row's seen IDs. -/
theorem coreOrderMemSeen9 {P : Params9} {n : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} {b : OddSites9 n} {c : I.ID}
    (hc : c ∈ coreOrder9 I v b) : c ∈ I.seen b.1 := by
  classical
  have hmem : c ∈ coreIDs9 I v b := by simpa [coreOrder9] using hc
  exact (Finset.mem_inter.mp (Finset.mem_erase.mp hmem).2).1

/-- Prefix restrictions of an ordered star row are fixed by its scope anchors. -/
theorem prefixLawEqOfAnchors9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) {b : OddSites9 n}
    (ω ω' : Outcome9 I N) (base base' : Law N) (hbase : base = base')
    (order : List I.ID) (horder : ∀ c ∈ order, c ∈ I.seen b.1)
    (hanc : ∀ c ∈ I.seen b.1, anc9 ω c = anc9 ω' c) (k : ℕ) :
    prefixLaw9 E G ω base order k = prefixLaw9 E G ω' base' order k := by
  classical
  have hids : ∀ c ∈ (order.take k).toFinset, c ∈ I.seen b.1 := by
    intro c hc
    apply horder c
    have hc' : c ∈ order.take k := by simpa using hc
    exact (List.take_sublist k order).subset hc'
  have hhit := hitSetEqOfAnchors9 E G ω ω' (order.take k).toFinset
    (fun c hc => hanc c (hids c hc))
  unfold prefixLaw9
  rw [hbase, hhit]

/-- Sequential regularity tests are invariant when all anchors in their order agree. -/
theorem orderRegularEqOfAnchors9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    (E : Fin N → Fin N → Prop) (G : Colour) {b : OddSites9 n}
    (ω ω' : Outcome9 I N) (base base' : Law N) (hbase : base = base')
    (order : List I.ID) (horder : ∀ c ∈ order, c ∈ I.seen b.1)
    (hanc : ∀ c ∈ I.seen b.1, anc9 ω c = anc9 ω' c) :
    orderRegular9 E G ω base order = orderRegular9 E G ω' base' order := by
  classical
  apply propext
  constructor
  · intro h k c hkc hprev
    have hc : c ∈ order := List.mem_of_getElem? hkc
    have hcSeen := horder c hc
    have hprev' : ∀ j c', j < k → order[j]? = some c' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω c')
          (prefixLaw9 E G ω base order j) := by
      intro j c' hj hjc
      have hc' : c' ∈ order := List.mem_of_getElem? hjc
      have hc'Seen := horder c' hc'
      have hpref := prefixLawEqOfAnchors9 E G ω ω' base base' hbase order horder hanc j
      have hbound := hprev j c' hj hjc
      rw [← hanc c' hc'Seen, ← hpref] at hbound
      exact hbound
    have hpref := prefixLawEqOfAnchors9 E G ω ω' base base' hbase order horder hanc k
    have hbound := h k c hkc hprev'
    rw [hanc c hcSeen, hpref] at hbound
    exact hbound
  · intro h k c hkc hprev
    have hc : c ∈ order := List.mem_of_getElem? hkc
    have hcSeen := horder c hc
    have hprev' : ∀ j c', j < k → order[j]? = some c' →
        (49 / 100 : ℝ) ≤ rowDeg E G (anc9 ω' c')
          (prefixLaw9 E G ω' base' order j) := by
      intro j c' hj hjc
      have hc' : c' ∈ order := List.mem_of_getElem? hjc
      have hc'Seen := horder c' hc'
      have hpref := prefixLawEqOfAnchors9 E G ω ω' base base' hbase order horder hanc j
      have hbound := hprev j c' hj hjc
      rw [hanc c' hc'Seen, hpref] at hbound
      exact hbound
    have hpref := prefixLawEqOfAnchors9 E G ω ω' base base' hbase order horder hanc k
    have hbound := h k c hkc hprev'
    rw [← hanc c hcSeen, ← hpref] at hbound
    exact hbound

/-- The three sequential regularity tests of a star depend only on its scope. -/
theorem starRegularEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) :
    starRegular9 S E G ω v = starRegular9 S E G ω' v := by
  classical
  have hanc (b : OddSites9 n) (hb : (cube n).Adj v.1 b.1) :
      ∀ c ∈ I.seen b.1, anc9 ω c = anc9 ω' c :=
    starScopeAnchorEq9 ω ω' hω b hb
  have hmask (b : OddSites9 n) (hb : (cube n).Adj v.1 b.1) :
      maskedLaw9 S ω b = maskedLaw9 S ω' b := by
    simp [maskedLaw9, starScopeMaskEq9 ω ω' hω b hb]
  have hfull (b : OddSites9 n) (hb : (cube n).Adj v.1 b.1) :
      ∀ c ∈ fullOrder9 I v b, c ∈ I.seen b.1 := fun c hc => fullOrderMemSeen9 hb hc
  have hcore (b : OddSites9 n) : ∀ c ∈ coreOrder9 I v b, c ∈ I.seen b.1 :=
    fun c hc => coreOrderMemSeen9 hc
  apply propext
  constructor
  · intro h b hb
    have he1 := orderRegularEqOfAnchors9 E G ω ω' (maskedLaw9 S ω b) (maskedLaw9 S ω' b)
      (hmask b hb) (fullOrder9 I v b) (hfull b hb) (hanc b hb)
    have he2 := orderRegularEqOfAnchors9 E G ω ω' (siteSecond9 S b.1) (siteSecond9 S b.1)
      rfl (fullOrder9 I v b) (hfull b hb) (hanc b hb)
    have he3 := orderRegularEqOfAnchors9 E G ω ω' (siteSecond9 S b.1) (siteSecond9 S b.1)
      rfl (coreOrder9 I v b) (hcore b) (hanc b hb)
    rcases h b hb with ⟨h1, h2, h3⟩
    exact ⟨he1.mp h1, he2.mp h2, he3.mp h3⟩
  · intro h b hb
    have he1 := orderRegularEqOfAnchors9 E G ω ω' (maskedLaw9 S ω b) (maskedLaw9 S ω' b)
      (hmask b hb) (fullOrder9 I v b) (hfull b hb) (hanc b hb)
    have he2 := orderRegularEqOfAnchors9 E G ω ω' (siteSecond9 S b.1) (siteSecond9 S b.1)
      rfl (fullOrder9 I v b) (hfull b hb) (hanc b hb)
    have he3 := orderRegularEqOfAnchors9 E G ω ω' (siteSecond9 S b.1) (siteSecond9 S b.1)
      rfl (coreOrder9 I v b) (hcore b) (hanc b hb)
    rcases h b hb with ⟨h1, h2, h3⟩
    exact ⟨he1.mpr h1, he2.mpr h2, he3.mpr h3⟩

/-- The log-gain and validity gate are fixed by a star scope. -/
theorem starGainEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) :
    starGain9 S E G ω v = starGain9 S E G ω' v := by
  classical
  unfold starGain9
  apply Finset.sum_congr rfl
  intro b hb
  have hcenter : anc9 ω (I.center v.1) = anc9 ω' (I.center v.1) :=
    starScopeAnchorEq9 ω ω' hω b.1 b.2 (I.center v.1) (centerSeen9 b.2)
  have hrows := starScopeRowsEq9 S E G ω ω' hω b.1 b.2
  simp [targetFrac9, hcenter, hrows.2 (I.center v.1)]

/-- The full star-validity predicate is fixed by a star scope. -/
theorem starValidEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) :
    starValid9 S E G ω v = starValid9 S E G ω' v := by
  unfold starValid9
  rw [starRegularEq9 S E G ω ω' hω, starGainEq9 S E G ω ω' hω]

/-- Replacing a star's target anchor preserves agreement on its scope. -/
theorem starScopeUpdAgree9 {P : Params9} {n N : ℕ} {I : IDMap9 P n}
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) (x : Fin N) :
    ∀ i ∈ starScope9 I v,
      updAnc9 ω (I.center v.1) x i = updAnc9 ω' (I.center v.1) x i := by
  classical
  intro i hi
  by_cases heq : i = Sum.inl (I.center v.1)
  · subst i
    change Function.update ω (Sum.inl (I.center v.1))
      (show Val9 I N (Sum.inl (I.center v.1)) from x) (Sum.inl (I.center v.1)) =
      Function.update ω' (Sum.inl (I.center v.1))
        (show Val9 I N (Sum.inl (I.center v.1)) from x) (Sum.inl (I.center v.1))
    rw [Function.update_self, Function.update_self]
  · change Function.update ω (Sum.inl (I.center v.1))
      (show Val9 I N (Sum.inl (I.center v.1)) from x) i =
      Function.update ω' (Sum.inl (I.center v.1))
        (show Val9 I N (Sum.inl (I.center v.1)) from x) i
    rw [Function.update_of_ne heq, Function.update_of_ne heq]
    exact hω i hi

/-- The gated row likelihoods on star data are fixed by the local scope. -/
theorem starScopeLikEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i)
    (x : Fin N) (ys : StarOdd9 v → Fin N) :
    starLik9 S E G ω v x ys = starLik9 S E G ω' v x ys := by
  classical
  let ωx := updAnc9 ω (I.center v.1) x
  let ω'x := updAnc9 ω' (I.center v.1) x
  have hupd := starScopeUpdAgree9 ω ω' hω x
  have hvalid := starValidEq9 S E G ωx ω'x hupd
  have hrow : ∀ b : StarOdd9 v, rowLaw9 S E G ωx b.1 = rowLaw9 S E G ω'x b.1 := by
    intro b
    exact (starScopeRowsEq9 S E G ωx ω'x hupd b.1 b.2).1
  simp [starLik9, ωx, ω'x, hvalid, hrow]

/-- The predictive marginal and deleted reference law on a star are fixed by its scope. -/
theorem starScopePosteriorEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) (ys : StarOdd9 v → Fin N) :
    starMarg9 S E G ω v ys = starMarg9 S E G ω' v ys ∧
      starRef9 S E G ω v ys = starRef9 S E G ω' v ys ∧
      predFail9 S E G ω v ys = predFail9 S E G ω' v ys := by
  classical
  have hMarg : starMarg9 S E G ω v ys = starMarg9 S E G ω' v ys := by
    unfold starMarg9
    apply Finset.sum_congr rfl
    intro x hx
    rw [starScopeLikEq9 S E G ω ω' hω x ys]
  have hRef : starRef9 S E G ω v ys = starRef9 S E G ω' v ys := by
    unfold starRef9
    apply Finset.prod_congr rfl
    intro b hb
    have hrows := starScopeRowsEq9 S E G ω ω' hω b.1 b.2
    exact congrArg (fun L : Law N => L.w (ys b)) (hrows.2 (I.center v.1))
  exact ⟨hMarg, hRef, by simp [predFail9, hMarg, hRef]⟩

/-- The alarm and bad-star event are fixed by a star scope. -/
theorem starScopeBadEq9 {P : Params9} {n N : ℕ} {M : TagMix N} {I : IDMap9 P n}
    (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    {v : EvenSites9 n} (ω ω' : Outcome9 I N)
    (hω : ∀ i ∈ starScope9 I v, ω i = ω' i) :
    StarBad9 S E G ω v = StarBad9 S E G ω' v := by
  classical
  by_cases hn : n = 0
  · subst n
    haveI : IsEmpty (OddSites9 0) := ⟨fun b => b.2 (by simp [IsEvenRole])⟩
    haveI : IsEmpty (StarOdd9 v) := ⟨fun b => isEmptyElim b.1⟩
    have hvalid (η : Outcome9 I N) : starValid9 S E G η v := by
      constructor
      · intro b hb
        exact isEmptyElim b
      · simp [starGain9, gainConst9]
    have hlik (η : Outcome9 I N) (x : Fin N) (ys : StarOdd9 v → Fin N) :
        starLik9 S E G η v x ys = 1 := by
      simp [starLik9, hvalid]
    have hmarg (η : Outcome9 I N) (ys : StarOdd9 v → Fin N) :
        starMarg9 S E G η v ys = 1 := by
      unfold starMarg9
      simp_rw [hlik]
      simpa using (siteFirst9 S v.1).sum_eq_one
    have href (η : Outcome9 I N) (ys : StarOdd9 v → Fin N) :
        starRef9 S E G η v ys = 1 := by simp [starRef9]
    have hfail (η : Outcome9 I N) (ys : StarOdd9 v → Fin N) :
        ¬ predFail9 S E G η v ys := by
      simp [predFail9, hmarg, href, Params9.tail, gainConst9]
    have halarm (η : Outcome9 I N) : alarm9 S E G η v = 0 := by
      simp [alarm9, hlik, hfail]
    have hbad (η : Outcome9 I N) : ¬ StarBad9 S E G η v := by
      simp [StarBad9, hvalid, halarm, Params9.tail, gainConst9]
    apply propext
    constructor
    · intro h
      exact (hbad ω h).elim
    · intro h
      exact (hbad ω' h).elim
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let j : Fin n := ⟨0, hnpos⟩
    have hodd : ¬ IsEvenRole (cubeFlip v.1 j) := by
      intro hflip
      exact (cubeFlip_parity v.1 j).mp hflip v.2
    let b : OddSites9 n := ⟨cubeFlip v.1 j, hodd⟩
    have hb : (cube n).Adj v.1 b.1 := cubeFlip_adj v.1 j
    have hcenter : anc9 ω (I.center v.1) = anc9 ω' (I.center v.1) :=
      starScopeAnchorEq9 ω ω' hω b hb (I.center v.1) (centerSeen9 hb)
    have hvalid := starValidEq9 S E G ω ω' hω
    have halarm : alarm9 S E G ω v = alarm9 S E G ω' v := by
      unfold alarm9
      apply Finset.sum_congr rfl
      intro ys hys
      have hposterior := starScopePosteriorEq9 S E G ω ω' hω ys
      have hlik := starScopeLikEq9 S E G ω ω' hω (anc9 ω (I.center v.1)) ys
      rw [← hcenter, hlik, hposterior.2.2]
    unfold StarBad9
    rw [hvalid, halarm]

end HypercubeRamsey.Lane_q_s09_assign1
