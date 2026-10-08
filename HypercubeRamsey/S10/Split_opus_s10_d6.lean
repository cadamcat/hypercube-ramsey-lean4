import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k
import HypercubeRamsey.S10.Split_opus_s10_tagged_q_s10_d10

/-!
# Lane opus-s10-d6: helpers for the likelihood comparison (10.2) (TeX 10:191–222)

Generic statements used by `Lane_opus_s10_tagged.d6_likelihood_comparison`. They do not
mention the tagged-system definitions (this file is imported by the tagged file):

* `group_ratio`: the per-group ratio of the restricted squared-tilt likelihood to the
  deletion reference, cluster by cluster (10:202–214);
* `untilted_mass_le`: the clusters dropped by the restrictions carry little squared mass
  (`h_F ≥ 1/2`, 10:131–142);
* `ratio_le_one_of_le_two`, `ratio_le_thr`: the factor `(D(F)/D(F_{-c}))^{2-j}`;
* `le_card_mul_avg`: one deletion reference is at most the list count times the uniform
  average (10:216);
* `card_powerset_filter_card_le`: the number of lists of bounded size;
* geometry of incident groups (singletons, 10:214).
-/

namespace HypercubeRamsey.Lane_opus_s10_d6

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

theorem lawMassOn_nonneg {N : ℕ} (D : Law N) (A : Finset (Fin N)) : 0 ≤ lawMassOn D A :=
  Finset.sum_nonneg fun y _ => D.nonneg y

theorem lawMassOn_mono {N : ℕ} (D : Law N) {A B : Finset (Fin N)} (h : A ⊆ B) :
    lawMassOn D A ≤ lawMassOn D B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun y _ _ => D.nonneg y

/-- The factor `(u/v)^2 (v/u)^s ≤ 1` for at most two labels (`u ≤ v`). -/
theorem ratio_le_one_of_le_two {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) {s : ℕ} (hs : s ≤ 2) :
    (u / v) ^ 2 * (v / u) ^ s ≤ 1 := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have h1 : u / v ≤ 1 := (div_le_one hv).mpr huv
  have h0 : 0 ≤ u / v := (div_pos hu hv).le
  have hinv : (v / u) ^ s = ((u / v) ^ s)⁻¹ := by rw [← inv_pow, inv_div]
  rw [hinv, ← div_eq_mul_inv]
  have hpos : 0 < (u / v) ^ s := pow_pos (div_pos hu hv) s
  rw [div_le_one hpos]
  exact pow_le_pow_of_le_one h0 h1 hs

/-- The factor `(u/v)^2 (v/u)^s ≤ thr^{-(s-2)}` under the ratio gate `thr·v ≤ u`. -/
theorem ratio_le_thr {u v thr : ℝ} (hu : 0 < u) (hthr : 0 < thr) (huv : u ≤ v)
    (h : thr * v ≤ u) {s : ℕ} (hs : 2 ≤ s) :
    (u / v) ^ 2 * (v / u) ^ s ≤ (1 / thr) ^ (s - 2) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  obtain ⟨e, rfl⟩ : ∃ e, s = 2 + e := ⟨s - 2, by omega⟩
  rw [pow_add, show 2 + e - 2 = e by omega]
  have h1 : (u / v) ^ 2 * (v / u) ^ 2 = 1 := by field_simp
  rw [← mul_assoc, h1, one_mul]
  apply pow_le_pow_left₀ (div_pos hv hu).le
  rw [div_le_div_iff₀ hu hthr]
  linarith

/-- From a ratio lower bound `e^x ≤ A/A'` to `A' ≤ e^{-x} A`. -/
theorem le_exp_neg_mul_of_ratio {A A' x : ℝ} (hA' : 0 < A') (h : Real.exp x ≤ A / A') :
    A' ≤ Real.exp (-x) * A := by
  rw [le_div_iff₀ hA'] at h
  rw [Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos x)]
  linarith

/-- Squared cluster mass is monotone in the set. -/
theorem sqMass_mono {N K : ℕ} (ρ : FinProb (Fin K)) (D : Fin K → Law N)
    {A B : Finset (Fin N)} (h : A ⊆ B) :
    ∑ j, ρ.w j * lawMassOn (D j) A ^ 2 ≤ ∑ j, ρ.w j * lawMassOn (D j) B ^ 2 :=
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (lawMassOn_nonneg _ _) (lawMassOn_mono _ h) 2) (ρ.nonneg j)

/-- Per-group likelihood ratio (10:202–214), cluster by cluster: the restricted
squared-tilt likelihood is at most `C·X` times the deletion reference, when the
reference normalizer is at most `C` times the retained tilt mass and every retained
cluster has `(D(F)/D(F_{-c}))^{2-j} ≤ X`. -/
theorem group_ratio {β : Type*} {N K : ℕ} (ρ : FinProb (Fin K)) (D : Fin K → Law N)
    (F Fm : Finset (Fin N)) (hsub : F ⊆ Fm) (kept : Finset (Fin K))
    (hpos : ∀ j ∈ kept, 0 < lawMassOn (D j) F)
    (lab rlab : Fin K → Law N)
    (hlab : ∀ j ∈ kept, ∀ y, (lab j).w y =
      if y ∈ F then (D j).w y / lawMassOn (D j) F else 0)
    (hrlab : ∀ j, 0 < lawMassOn (D j) Fm → ∀ y, (rlab j).w y =
      if y ∈ Fm then (D j).w y / lawMassOn (D j) Fm else 0)
    (B : Finset β) (ω : β → Fin N) (X C : ℝ) (hX0 : 0 ≤ X)
    (hX : ∀ j ∈ kept, (lawMassOn (D j) F / lawMassOn (D j) Fm) ^ 2 *
      (lawMassOn (D j) Fm / lawMassOn (D j) F) ^ B.card ≤ X)
    (hT : 0 < ∑ j, (if j ∈ kept then ρ.w j * lawMassOn (D j) F ^ 2 else 0))
    (hC : ∑ j, ρ.w j * lawMassOn (D j) Fm ^ 2 ≤
      C * ∑ j, (if j ∈ kept then ρ.w j * lawMassOn (D j) F ^ 2 else 0)) :
    ∑ j, ((if j ∈ kept then ρ.w j * lawMassOn (D j) F ^ 2 else 0) /
        ∑ j', (if j' ∈ kept then ρ.w j' * lawMassOn (D j') F ^ 2 else 0)) *
        ∏ b ∈ B, (lab j).w (ω b) ≤
      C * X * ∑ j, (ρ.w j * lawMassOn (D j) Fm ^ 2 /
        ∑ j', ρ.w j' * lawMassOn (D j') Fm ^ 2) * ∏ b ∈ B, (rlab j).w (ω b) := by
  set T := ∑ j, (if j ∈ kept then ρ.w j * lawMassOn (D j) F ^ 2 else 0) with hTdef
  set A := ∑ j, ρ.w j * lawMassOn (D j) Fm ^ 2 with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => mul_nonneg (ρ.nonneg j) (sq_nonneg _)
  have hC0 : 0 ≤ C := by
    by_contra hneg
    push_neg at hneg
    have : C * T < 0 := mul_neg_of_neg_of_pos hneg hT
    linarith
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have href0 : 0 ≤ (ρ.w j * lawMassOn (D j) Fm ^ 2 / A) * ∏ b ∈ B, (rlab j).w (ω b) :=
    mul_nonneg (div_nonneg (mul_nonneg (ρ.nonneg j) (sq_nonneg _)) hA0)
      (Finset.prod_nonneg fun b _ => (rlab j).nonneg _)
  by_cases hj : j ∈ kept
  swap
  · simp only [hj, if_false, zero_div, zero_mul]
    exact mul_nonneg (mul_nonneg hC0 hX0) href0
  simp only [hj, if_true]
  have hu := hpos j hj
  have hXj := hX j hj
  set u := lawMassOn (D j) F with hudef
  set v := lawMassOn (D j) Fm with hvdef
  have huv : u ≤ v := lawMassOn_mono (D j) hsub
  have hv : 0 < v := lt_of_lt_of_le hu huv
  by_cases hall : ∀ b ∈ B, ω b ∈ F
  swap
  · push_neg at hall
    obtain ⟨b, hb, hbF⟩ := hall
    have hzero : ∏ b ∈ B, (lab j).w (ω b) = 0 :=
      Finset.prod_eq_zero hb (by rw [hlab j hj, if_neg hbF])
    rw [hzero, mul_zero]
    exact mul_nonneg (mul_nonneg hC0 hX0) href0
  set P := ∏ b ∈ B, (D j).w (ω b) with hPdef
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun b _ => (D j).nonneg _
  have hlabP : ∏ b ∈ B, (lab j).w (ω b) = P / u ^ B.card := by
    calc
      ∏ b ∈ B, (lab j).w (ω b) = ∏ b ∈ B, ((D j).w (ω b) / u) :=
        Finset.prod_congr rfl fun b hb => by rw [hlab j hj, if_pos (hall b hb)]
      _ = P / u ^ B.card := by rw [Finset.prod_div_distrib, Finset.prod_const]
  have hrlabP : ∏ b ∈ B, (rlab j).w (ω b) = P / v ^ B.card := by
    calc
      ∏ b ∈ B, (rlab j).w (ω b) = ∏ b ∈ B, ((D j).w (ω b) / v) :=
        Finset.prod_congr rfl fun b hb => by rw [hrlab j hv, if_pos (hsub (hall b hb))]
      _ = P / v ^ B.card := by rw [Finset.prod_div_distrib, Finset.prod_const]
  rw [hlabP, hrlabP]
  by_cases hρ : ρ.w j = 0
  · rw [hρ]
    simp only [zero_mul, zero_div, mul_zero]
    exact le_rfl
  have hρpos : 0 < ρ.w j := lt_of_le_of_ne (ρ.nonneg j) (Ne.symm hρ)
  have hApos : 0 < A := by
    have hle : ρ.w j * v ^ 2 ≤ A :=
      Finset.single_le_sum (f := fun j => ρ.w j * lawMassOn (D j) Fm ^ 2)
        (fun j _ => mul_nonneg (ρ.nonneg j) (sq_nonneg _)) (Finset.mem_univ j)
    have : 0 < ρ.w j * v ^ 2 := mul_pos hρpos (pow_pos hv 2)
    linarith
  have hid : ρ.w j * u ^ 2 / T * (P / u ^ B.card) =
      (A / T) * ((u / v) ^ 2 * (v / u) ^ B.card) *
        (ρ.w j * v ^ 2 / A * (P / v ^ B.card)) := by
    have hu' := hu.ne'
    have hv' := hv.ne'
    have hA' := hApos.ne'
    have hT' := hT.ne'
    rw [div_pow, div_pow]
    field_simp
  rw [hid]
  have hAT : A / T ≤ C := by rw [div_le_iff₀ hT]; linarith
  have hratio0 : 0 ≤ (u / v) ^ 2 * (v / u) ^ B.card :=
    mul_nonneg (sq_nonneg _) (pow_nonneg (div_pos hv hu).le _)
  have hrefj : 0 ≤ ρ.w j * v ^ 2 / A * (P / v ^ B.card) :=
    mul_nonneg (div_nonneg (mul_nonneg hρpos.le (sq_nonneg _)) hApos.le)
      (div_nonneg hP0 (pow_nonneg hv.le _))
  apply mul_le_mul_of_nonneg_right _ hrefj
  exact mul_le_mul hAT hXj hratio0 hC0

/-- The clusters dropped by the absolute-mass and deletion-ratio restrictions carry
squared mass at most `e0² + Σ_c thr_c² A(F_{-c})` (10:136–142). -/
theorem untilted_mass_le {ι : Type*} {N K : ℕ} (ρ : FinProb (Fin K)) (D : Fin K → Law N)
    (F : Finset (Fin N)) (Fm : ι → Finset (Fin N)) (L : Finset ι) (thr : ι → ℝ) (e0 : ℝ)
    (kept : Finset (Fin K))
    (hkept : ∀ j, j ∉ kept → lawMassOn (D j) F < e0 ∨
      ∃ c ∈ L, lawMassOn (D j) F < thr c * lawMassOn (D j) (Fm c)) :
    ∑ j, ρ.w j * lawMassOn (D j) F ^ 2 ≤
      ∑ j, (if j ∈ kept then ρ.w j * lawMassOn (D j) F ^ 2 else 0) +
      (e0 ^ 2 + ∑ c ∈ L, thr c ^ 2 * ∑ j, ρ.w j * lawMassOn (D j) (Fm c) ^ 2) := by
  have hpt : ∀ j, ρ.w j * lawMassOn (D j) F ^ 2 ≤
      (if j ∈ kept then ρ.w j * lawMassOn (D j) F ^ 2 else 0) +
      (ρ.w j * e0 ^ 2 + ∑ c ∈ L, thr c ^ 2 * (ρ.w j * lawMassOn (D j) (Fm c) ^ 2)) := by
    intro j
    have hρ := ρ.nonneg j
    have hu := lawMassOn_nonneg (D j) F
    have hsum0 : 0 ≤ ∑ c ∈ L, thr c ^ 2 * (ρ.w j * lawMassOn (D j) (Fm c) ^ 2) :=
      Finset.sum_nonneg fun c _ => mul_nonneg (sq_nonneg _) (mul_nonneg hρ (sq_nonneg _))
    have he : 0 ≤ ρ.w j * e0 ^ 2 := mul_nonneg hρ (sq_nonneg _)
    by_cases hj : j ∈ kept
    · simp only [hj, if_true]
      linarith
    · simp only [hj, if_false, zero_add]
      rcases hkept j hj with h | ⟨c, hc, h⟩
      · have hsq : lawMassOn (D j) F ^ 2 ≤ e0 ^ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_left hsq hρ
        linarith
      · have hsq : lawMassOn (D j) F ^ 2 ≤ thr c ^ 2 * lawMassOn (D j) (Fm c) ^ 2 := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ hu h.le 2
        have hterm : ρ.w j * lawMassOn (D j) F ^ 2 ≤
            thr c ^ 2 * (ρ.w j * lawMassOn (D j) (Fm c) ^ 2) := by
          calc
            ρ.w j * lawMassOn (D j) F ^ 2 ≤
                ρ.w j * (thr c ^ 2 * lawMassOn (D j) (Fm c) ^ 2) :=
              mul_le_mul_of_nonneg_left hsq hρ
            _ = thr c ^ 2 * (ρ.w j * lawMassOn (D j) (Fm c) ^ 2) := by ring
        have hle := Finset.single_le_sum
          (f := fun c => thr c ^ 2 * (ρ.w j * lawMassOn (D j) (Fm c) ^ 2))
          (fun c _ => mul_nonneg (sq_nonneg _) (mul_nonneg hρ (sq_nonneg _))) hc
        linarith
  calc
    ∑ j, ρ.w j * lawMassOn (D j) F ^ 2 ≤
        ∑ j, ((if j ∈ kept then ρ.w j * lawMassOn (D j) F ^ 2 else 0) +
          (ρ.w j * e0 ^ 2 +
            ∑ c ∈ L, thr c ^ 2 * (ρ.w j * lawMassOn (D j) (Fm c) ^ 2))) :=
      Finset.sum_le_sum fun j _ => hpt j
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ρ.sum_eq_one,
        one_mul, Finset.sum_comm]
      congr 2
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]

/-- One member of a uniform average is at most the count times the average (10:216). -/
theorem le_card_mul_avg {α : Type*} (S : Finset α) (f : α → ℝ) (hf : ∀ x ∈ S, 0 ≤ f x)
    {x : α} (hx : x ∈ S) :
    f x ≤ (S.card : ℝ) * ((S.card : ℝ)⁻¹ * ∑ y ∈ S, f y) := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
  rw [← mul_assoc, mul_inv_cancel₀ hcard.ne', one_mul]
  exact Finset.single_le_sum hf hx

/-- Subsets of `s` with at most `K` elements number at most `(|s|+1)^K`. -/
theorem card_powerset_filter_card_le {α : Type*} [DecidableEq α] (s : Finset α) (K : ℕ) :
    ((s.powerset.filter fun L => L.card ≤ K).card) ≤ (s.card + 1) ^ K := by
  let g : (Fin K → Option s) → Finset α := fun f =>
    Finset.univ.biUnion fun i => (f i).elim ∅ fun x => {x.1}
  have hsurj : (s.powerset.filter fun L => L.card ≤ K) ⊆ Finset.univ.image g := by
    intro L hL
    obtain ⟨hLs, hLK⟩ := Finset.mem_filter.mp hL
    have hLs' : L ⊆ s := Finset.mem_powerset.mp hLs
    let f : Fin K → Option s := fun i =>
      if h : i.1 < L.card then
        some ⟨(L.equivFin.symm ⟨i.1, h⟩).1, hLs' (L.equivFin.symm ⟨i.1, h⟩).2⟩
      else none
    refine Finset.mem_image.mpr ⟨f, Finset.mem_univ _, ?_⟩
    ext x
    simp only [g, f, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      by_cases h : i.1 < L.card
      · simp only [h, dif_pos, Option.elim, Finset.mem_singleton] at hi
        rw [hi]
        exact (L.equivFin.symm ⟨i.1, h⟩).2
      · simp [h] at hi
    · intro hx
      let i0 := L.equivFin ⟨x, hx⟩
      refine ⟨⟨i0.1, lt_of_lt_of_le i0.2 hLK⟩, ?_⟩
      have h : i0.1 < L.card := i0.2
      simp only [h, dif_pos, Option.elim, Finset.mem_singleton]
      have : L.equivFin.symm ⟨i0.1, h⟩ = ⟨x, hx⟩ := by
        simp [i0]
      rw [this]
  calc
    (s.powerset.filter fun L => L.card ≤ K).card ≤ (Finset.univ.image g).card :=
      Finset.card_le_card hsurj
    _ ≤ (Finset.univ : Finset (Fin K → Option s)).card := Finset.card_image_le
    _ = (s.card + 1) ^ K := by simp

/-! ### Geometry of the incident groups (10:214) -/

/-- A word at Hamming distance one is a one-coordinate flip (public copy). -/
theorem flip_of_hammingDist_one {d : ℕ} (s t : Fin d → Bool)
    (h : _root_.hammingDist s t = 1) :
    ∃ j : Fin d, t = p10_1kFlipCoordinate s j := by
  classical
  have hcard : (Finset.univ.filter (fun i : Fin d => s i ≠ t i)).card = 1 := by
    simpa [_root_.hammingDist] using h
  obtain ⟨j, hfilter⟩ := Finset.card_eq_one.mp hcard
  refine ⟨j, ?_⟩
  funext k
  have hk : s k ≠ t k ↔ k = j := by
    have hmem : k ∈ Finset.univ.filter (fun i : Fin d => s i ≠ t i) ↔ k = j := by
      rw [hfilter]
      simp
    simpa using hmem
  by_cases hkj : k = j
  · subst k
    have hne : s j ≠ t j := hk.2 rfl
    cases hs : s j <;> cases ht : t j <;> simp_all [p10_1kFlipCoordinate]
  · have heq : s k = t k := by
      by_contra hne
      exact hkj (hk.1 hne)
    simp [p10_1kFlipCoordinate, hkj, heq]

/-- At most `m` words are at Hamming distance one from a word of length `m`. -/
theorem card_dist_one_le {m : ℕ} (z : Fin m → Bool) :
    (Finset.univ.filter fun z' : Fin m → Bool => _root_.hammingDist z z' = 1).card ≤ m := by
  classical
  have hsubset : (Finset.univ.filter fun z' : Fin m → Bool => _root_.hammingDist z z' = 1) ⊆
      (Finset.univ : Finset (Fin m)).image (p10_1kFlipCoordinate z) := by
    intro z' hz'
    obtain ⟨j, hflip⟩ := flip_of_hammingDist_one z z' (Finset.mem_filter.mp hz').2
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hflip.symm⟩
  calc
    _ ≤ ((Finset.univ : Finset (Fin m)).image (p10_1kFlipCoordinate z)).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
    _ = m := by simp

/-- The projected site of an even role lies in the envelope of each incident group
and is a projected even site of its slice. -/
theorem evenVertex_mem_incident {n m : ℕ} (hm : m ≤ n) (a : P10_1kEvenRole n)
    (q : P10_1kProjectedSite n m) (hq : q ∈ p10_1kIncidentOddGroups hm a) :
    p10_1kProjectedVertex hm a.1 ∈ p10_1kProjectedNeighborEnvelope q ∧
      (p10_1kProjectedVertex hm a.1).2 ∈
        p10_1kProjectedEvenSites hm (p10_1kProjectedVertex hm a.1).1 := by
  obtain ⟨b, hadj, hbq⟩ := (p10_1k_mem_incidentOddGroups hm a q).mp hq
  refine ⟨?_, p10_1kProjectedEvenRole_mem_sites hm a⟩
  have := p10_1k_evenSite_mem_oddGroupEnvelope_of_adjacent hm a b hadj
  rwa [hbq] at this

/-- A group in an adjacent special slice meets the star in at most one role. -/
theorem star_filter_card_le_one_of_special {n m : ℕ} (hm : m ≤ n) (a : P10_1kEvenRole n)
    (q : P10_1kProjectedSite n m) (hq : q.1 ≠ (p10_1kProjectedVertex hm a.1).1) :
    ((Finset.univ.filter fun b : P10_1kOddRole n => (cube n).Adj a.1 b.1).filter
      fun b => p10_1kProjectedVertex hm b.1 = q).card ≤ 1 := by
  classical
  have h := p10_1k_specialIncidentOddGroup_card_le_one hm a q hq
  rw [Fintype.card_coe] at h
  have heq : ((Finset.univ.filter fun b : P10_1kOddRole n => (cube n).Adj a.1 b.1).filter
      fun b => p10_1kProjectedVertex hm b.1 = q) = p10_1kSpecialIncidentOddGroup hm a q := by
    ext b
    simp [p10_1kSpecialIncidentOddGroup]
  rw [heq]
  exact h

/-- In a chunk with at least two coordinates every projected neighbor is shared by a
second coordinate. -/
theorem chunk_partner {G : Type} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (h₂ : ∀ g : G, g + g = 0) (s : G → Bool) (g : G) (hG : 2 ≤ Fintype.card G) :
    ∃ g', g' ≠ g ∧ projectedNeighbor s g' = projectedNeighbor s g := by
  classical
  have hcard := p10_1k_local_projectedNeighbor_fiber_card h₂ s (projectedNeighbor s g)
    ⟨g, rfl⟩
  have h1 : 1 < Fintype.card {g' : G // projectedNeighbor s g' = projectedNeighbor s g} := by
    rw [hcard]
    split_ifs <;> omega
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card h1 ⟨g, rfl⟩
  exact ⟨x.1, fun h => hx (Subtype.ext h), x.2⟩

theorem changed_chunk_of_eq (d : ℕ) (s : Fin d → Bool) (j : Fin d)
    (i : Fin d.bitIndices.length) (g : P10_1kChunkGroup d i)
    (h : p10_1k_chunkCoordinateEquiv d j = ⟨i, g⟩) :
    p10_1k_chunkedWord d (p10_1k_projectedWord d (p10_1kFlipCoordinate s j)) i =
      projectedNeighbor (p10_1k_chunkedWord d s i) g := by
  have := p10_1k_projectedWord_flip_changed_chunk d s j
  rw [h] at this
  exact this

/-- A residual coordinate in a chunk of size at least two has a partner coordinate whose
flip projects to the same site. -/
theorem residual_partner (d : ℕ) (s : Fin d → Bool) (j : Fin d)
    (hsize : d.bitIndices.get (p10_1k_chunkCoordinateEquiv d j).1 ≠ 0) :
    ∃ k, k ≠ j ∧ p10_1k_projectedWord d (p10_1kFlipCoordinate s k) =
      p10_1k_projectedWord d (p10_1kFlipCoordinate s j) := by
  classical
  set e := p10_1k_chunkCoordinateEquiv d with he
  set i := (e j).1 with hi
  have hG : 2 ≤ Fintype.card (P10_1kChunkGroup d i) := by
    simp only [P10_1kChunkGroup, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have : 1 ≤ d.bitIndices.get i := Nat.one_le_iff_ne_zero.mpr hsize
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d.bitIndices.get i := Nat.pow_le_pow_right (by norm_num) this
  obtain ⟨g', hg'ne, hg'eq⟩ := chunk_partner (p10_1k_chunkGroup_two_add d i)
    (p10_1k_chunkedWord d s i) (e j).2 hG
  have hek : e (e.symm ⟨i, g'⟩) = ⟨i, g'⟩ := Equiv.apply_symm_apply e _
  have hej : e j = ⟨i, (e j).2⟩ := rfl
  refine ⟨e.symm ⟨i, g'⟩, ?_, ?_⟩
  · intro h
    apply hg'ne
    have h2 : (⟨i, g'⟩ : P10_1kChunkCoordinate d) = ⟨i, (e j).2⟩ := by
      rw [← hek, h]
    exact eq_of_heq (Sigma.mk.inj h2).2
  · apply (p10_1kChunkFamilyEquiv d).injective
    rw [← p10_1k_chunkedWord_eq_familyEquiv, ← p10_1k_chunkedWord_eq_familyEquiv]
    funext i'
    by_cases hii : i' = i
    · subst hii
      rw [changed_chunk_of_eq d s _ _ g' hek, changed_chunk_of_eq d s j _ (e j).2 hej]
      exact hg'eq
    · have hk1 : i' ≠ (e (e.symm ⟨i, g'⟩)).1 := by rw [hek]; exact hii
      rw [p10_1k_projectedWord_flip_unchanged_chunk d s _ i' hk1,
        p10_1k_projectedWord_flip_unchanged_chunk d s j i' hii]

/-- Incident groups that are not ordinary own-slice groups with at least two star
roles: at most `m` adjacent-slice groups and one residual singleton per size-one
chunk (10:214, "at most `m+1` singleton groups"). -/
theorem bad_groups_card_le {n m : ℕ} (hm : m ≤ n) (a : P10_1kEvenRole n) :
    ((p10_1kIncidentOddGroups hm a).filter fun q =>
      ¬ (q.1 = (p10_1kProjectedVertex hm a.1).1 ∧
        2 ≤ ((Finset.univ.filter fun b : P10_1kOddRole n => (cube n).Adj a.1 b.1).filter
          fun b => p10_1kProjectedVertex hm b.1 = q).card)).card ≤ m + (Nat.log 2 n + 1) := by
  classical
  set I := p10_1kIncidentOddGroups hm a with hIdef
  set sa := (p10_1kProjectedVertex hm a.1).1 with hsadef
  set star := Finset.univ.filter fun b : P10_1kOddRole n => (cube n).Adj a.1 b.1 with hstar
  have hsplit : (I.filter fun q => ¬ (q.1 = sa ∧
      2 ≤ (star.filter fun b => p10_1kProjectedVertex hm b.1 = q).card)) ⊆
      (I.filter fun q => q.1 ≠ sa) ∪ (I.filter fun q => q.1 = sa ∧
        (star.filter fun b => p10_1kProjectedVertex hm b.1 = q).card ≤ 1) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases h1 : q.1 = sa
    · right
      refine ⟨hq.1, h1, ?_⟩
      have := hq.2
      push_neg at this
      have := this h1
      omega
    · left
      exact ⟨hq.1, h1⟩
  have hspecial : (I.filter fun q => q.1 ≠ sa).card ≤ m := by
    have hsub : (I.filter fun q => q.1 ≠ sa) ⊆
        (Finset.univ.filter fun z : Fin m → Bool => _root_.hammingDist sa z = 1).image
          (fun z => (z, (p10_1kProjectedVertex hm a.1).2)) := by
      intro q hq
      obtain ⟨hqI, hne⟩ := Finset.mem_filter.mp hq
      have henv := p10_1k_incidentOddGroups_subset_envelope hm a hqI
      unfold p10_1kProjectedNeighborEnvelope at henv
      rcases Finset.mem_union.mp henv with hs | hr
      · exact hs
      · obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hr
        exact absurd (by rw [← ht]) hne
    calc
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_image_le
      _ ≤ m := card_dist_one_le sa
  have hres : (I.filter fun q => q.1 = sa ∧
      (star.filter fun b => p10_1kProjectedVertex hm b.1 = q).card ≤ 1).card ≤
        Nat.log 2 n + 1 := by
    set d := n - m with hd
    set e := p10_1k_chunkCoordinateEquiv d with he
    set ra := p10_1kResidualWord hm a.1 with hra
    let J1 : Finset (Fin d) := Finset.univ.filter fun j => d.bitIndices.get (e j).1 = 0
    have hsub : (I.filter fun q => q.1 = sa ∧
        (star.filter fun b => p10_1kProjectedVertex hm b.1 = q).card ≤ 1) ⊆
        J1.image (fun j => (sa, p10_1k_projectedWord d (p10_1kFlipCoordinate ra j))) := by
      intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨hqI, hqa, hsq⟩ := hq
      obtain ⟨b, hadj, hbq⟩ := (p10_1k_mem_incidentOddGroups hm a q).mp hqI
      have hslice : p10_1kSpecialSlice hm a.1 = p10_1kSpecialSlice hm b.1 := by
        have h1 : (p10_1kProjectedVertex hm b.1).1 = q.1 := congrArg Prod.fst hbq
        rw [hqa] at h1
        exact h1.symm
      obtain ⟨j, hj⟩ := p10_1k_adjacent_residual_same_slice_flip hm hadj hslice
      have hq_eq : q = (sa, p10_1k_projectedWord d (p10_1kFlipCoordinate ra j)) := by
        rw [← hbq]
        apply Prod.ext
        · exact hslice.symm
        · change p10_1k_projectedWord (n - m) (p10_1kResidualWord hm b.1) = _
          rw [hj]
      refine Finset.mem_image.mpr ⟨j, ?_, hq_eq.symm⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hsize
      obtain ⟨k, hkj, hkeq⟩ := residual_partner d ra j hsize
      set b' := p10_1kResidualFlipOddRole hm a k with hb'
      have hb'site : p10_1kProjectedVertex hm b'.1 = q := by
        rw [hb', p10_1kResidualFlipOddRole_site, hq_eq, hkeq]
        rfl
      have hb'adj : (cube n).Adj a.1 b'.1 := p10_1kResidualFlipVertex_adjacent hm a.1 k
      have hbb' : b ≠ b' := by
        intro hbb
        have hres1 : p10_1kResidualWord hm b.1 = p10_1kResidualWord hm b'.1 := by rw [hbb]
        rw [hj] at hres1
        have hres2 : p10_1kResidualWord hm b'.1 = p10_1kFlipCoordinate ra k := by
          rw [hb']
          exact p10_1kResidualFlipVertex_residualWord hm a.1 k
        rw [hres2] at hres1
        have hbit := congrFun hres1 j
        simp [p10_1kFlipCoordinate, Ne.symm hkj] at hbit
        rw [← hra] at hbit
        cases hrj : ra j <;> rw [hrj] at hbit <;> simp at hbit
      have h2 : 2 ≤ (star.filter fun b => p10_1kProjectedVertex hm b.1 = q).card := by
        have hsub2 : ({b, b'} : Finset (P10_1kOddRole n)) ⊆
            star.filter fun b => p10_1kProjectedVertex hm b.1 = q := by
          intro x hx
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩, hbq⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'adj⟩,
              hb'site⟩
        have := Finset.card_le_card hsub2
        rw [Finset.card_pair hbb'] at this
        exact this
      omega
    have key : ∀ x y : P10_1kChunkCoordinate d, x.1 = y.1 → d.bitIndices.get x.1 = 0 →
        x = y := by
      rintro ⟨i, g⟩ ⟨i', g'⟩ h hz
      simp only at h
      subst h
      congr
      funext z
      have hz' : d.bitIndices.get i = 0 := hz
      have hz2 := z.2
      omega
    have hinj : Set.InjOn (fun j => (e j).1) J1 := by
      intro j hj j' _ hjj
      apply e.injective
      exact key _ _ hjj (Finset.mem_filter.mp hj).2
    calc
      _ ≤ (J1.image fun j => (sa, p10_1k_projectedWord d (p10_1kFlipCoordinate ra j))).card :=
        Finset.card_le_card hsub
      _ ≤ J1.card := Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin d.bitIndices.length)).card :=
        Finset.card_le_card_of_injOn (fun j => (e j).1) (fun _ _ => Finset.mem_univ _) hinj
      _ = d.bitIndices.length := by simp
      _ ≤ Nat.log 2 d + 1 := Lane_q_s10_d10.bitIndices_length_le_log d
      _ ≤ Nat.log 2 n + 1 := Nat.add_le_add_right (Nat.log_mono_right (Nat.sub_le n m)) 1
  calc
    _ ≤ _ := Finset.card_le_card hsplit
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ m + (Nat.log 2 n + 1) := Nat.add_le_add hspecial hres

/-! ### The exponent budget (10:218–222) -/

open Lane_q_s10_d10 in
/-- The numerical facts used by d6, eventually in `n`: `a ≤ 1/10`, `k ≥ 2`, the
retained-tilt bound `e^{-k} + (T+m)e^{-.24ak} ≤ 1/2`, and the final exponent budget
`n log 2 + 2k(m + log₂n + 1) + n(T+m) log(C+1) ≤ .02akn` with the candidate bound
`C = (m + (n+1)³)(H+1)·2λ`. -/
theorem d6_budget_eventually (δ : ℝ) (hδ : 0 < δ) (hδs : δ < 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-δ) ≤ 1 / 10 ∧
      (2 : ℝ) ≤ (p10_1kTupleListLength n δ : ℝ) ∧
      Real.exp (-(p10_1kTupleListLength n δ : ℝ)) +
          ((p10_1kHeightCount n δ : ℝ) + ((min (p10_1kSpecialCount n δ) n : ℕ) : ℝ)) *
            Real.exp (-(24 / 100 : ℝ) * (n : ℝ) ^ (-δ) *
              (p10_1kTupleListLength n δ : ℝ)) ≤ 1 / 2 ∧
      (n : ℝ) * Real.log 2 +
          2 * (p10_1kTupleListLength n δ : ℝ) *
            (((min (p10_1kSpecialCount n δ) n : ℕ) : ℝ) + ((Nat.log 2 n : ℝ) + 1)) +
          (n : ℝ) * (((p10_1kHeightCount n δ + min (p10_1kSpecialCount n δ) n : ℕ) : ℝ) *
            Real.log ((((min (p10_1kSpecialCount n δ) n : ℕ) : ℝ) + ((n : ℝ) + 1) ^ 3) *
              ((topScale n δ (8 * δ) : ℝ) + 1) * (2 * (n : ℝ) ^ 10) + 1)) ≤
        (2 / 100 : ℝ) * (n : ℝ) ^ (-δ) * (p10_1kTupleListLength n δ : ℝ) * n := by
  have hncast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hneg : Tendsto (fun n : ℕ => (n : ℝ) ^ (-δ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hδ).comp hncast
  have hdecay := power_exp_decay (a := 299 * δ) (b := 200 * δ) (c := 24 / 100)
    (by positivity) (by norm_num)
  filter_upwards [hneg.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10)),
    hncast.eventually ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 300 * δ)).eventually_ge_atTop 2),
    hncast.eventually (eventually_ge_atTop (2 : ℝ)),
    hdecay.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 12)),
    hncast.eventually ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 299 * δ)).eventually_ge_atTop 150),
    power_le_linear_eventually (a := 201 * δ) (c := 1200) (by linarith) (by norm_num),
    power_le_power_eventually (a := 201 * δ) (b := 299 * δ) (c := 17100 / δ) (by linarith)
      (by positivity),
    natLog_add_one_le_rpow_eventually (100 * δ) (by positivity),
    topScale_power_bound δ (8 * δ) hδ (by linarith)]
    with n ha hk2' hx2 hdec h150 hlin hpow hlogn hH
  set x : ℝ := (n : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set k : ℝ := (p10_1kTupleListLength n δ : ℝ) with hkdef
  have hkb := ceil_power_bounds hx1 (by positivity : (0 : ℝ) ≤ 300 * δ)
  have hk_lo : x ^ (300 * δ) ≤ k := hkb.1
  have hk_hi : k ≤ 2 * x ^ (300 * δ) := hkb.2
  set m : ℝ := ((min (p10_1kSpecialCount n δ) n : ℕ) : ℝ) with hmdef
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hm : m ≤ x ^ (200 * δ) := by
    have h1 : m ≤ (p10_1kSpecialCount n δ : ℝ) := by
      rw [hmdef]; exact_mod_cast min_le_left _ _
    exact h1.trans (Nat.floor_le (by positivity))
  set T : ℝ := (p10_1kHeightCount n δ : ℝ) with hTdef
  have hT0 : 0 ≤ T := Nat.cast_nonneg _
  have hT : T ≤ 2 * x ^ (200 * δ) := by
    have h1 := (ceil_power_bounds hx1 (by positivity : (0 : ℝ) ≤ 141 * δ)).2
    have h2 : x ^ (141 * δ) ≤ x ^ (200 * δ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    exact h1.trans (by linarith)
  have hp200 : 1 ≤ x ^ (200 * δ) := Real.one_le_rpow hx1 (by positivity)
  have hak : x ^ (299 * δ) ≤ x ^ (-δ) * k := by
    have hsplit : x ^ (299 * δ) = x ^ (-δ) * x ^ (300 * δ) := by
      rw [← Real.rpow_add hx0]; ring_nf
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hk_lo (by positivity)
  have hk2 : (2 : ℝ) ≤ k := hk2'.trans hk_lo
  refine ⟨ha, hk2, ?_, ?_⟩
  · -- retained tilt mass
    have he1 : Real.exp (-k) ≤ 1 / 4 := by
      have : Real.exp (-k) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (-2) < 1 / 4 := by
        have := Real.exp_one_gt_d9
        rw [show (-2 : ℝ) = -(1 + 1) by norm_num, Real.exp_neg, Real.exp_add]
        rw [inv_lt_comm₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have he2 : Real.exp (-(24 / 100 : ℝ) * x ^ (-δ) * k) ≤
        Real.exp (-(24 / 100 : ℝ) * x ^ (299 * δ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hdec' : x ^ (200 * δ) * Real.exp (-(24 / 100 : ℝ) * x ^ (299 * δ)) ≤ 1 / 12 := hdec
    have hTm : T + m ≤ 3 * x ^ (200 * δ) := by linarith
    have hE0 : 0 ≤ Real.exp (-(24 / 100 : ℝ) * x ^ (-δ) * k) := (Real.exp_pos _).le
    calc
      Real.exp (-k) + (T + m) * Real.exp (-(24 / 100 : ℝ) * x ^ (-δ) * k) ≤
          1 / 4 + 3 * x ^ (200 * δ) * Real.exp (-(24 / 100 : ℝ) * x ^ (299 * δ)) := by
        have := mul_le_mul hTm he2 hE0 (by positivity)
        linarith
      _ ≤ 1 / 2 := by linarith
  · -- the exponent budget
    have hlogn' : (Nat.log 2 n : ℝ) + 1 ≤ x ^ (200 * δ) := by
      have : (2 : ℝ) * (100 * δ) = 200 * δ := by ring
      rw [this] at hlogn
      exact hlogn
    have hH' : (topScale n δ (8 * δ) : ℝ) ≤ 4 * x := by
      have h1 : x ^ (1 - 8 * δ + δ) ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      rw [Real.rpow_one] at h1
      linarith
    have hH0 : (0 : ℝ) ≤ (topScale n δ (8 * δ) : ℝ) := Nat.cast_nonneg _
    -- the candidate bound
    set Cc : ℝ := (m + (x + 1) ^ 3) * ((topScale n δ (8 * δ) : ℝ) + 1) *
      (2 * x ^ 10) with hCcdef
    have hCc0 : 0 ≤ Cc := by positivity
    have hm_x : m ≤ x := by
      rw [hmdef, hxdef]; exact_mod_cast min_le_right _ _
    have hCc : Cc + 1 ≤ (x + 1) ^ 19 := by
      have h1 : m + (x + 1) ^ 3 ≤ 2 * (x + 1) ^ 3 := by
        have : x + 1 ≤ (x + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
        linarith
      have h2 : (topScale n δ (8 * δ) : ℝ) + 1 ≤ 4 * (x + 1) := by linarith
      have h3 : 2 * x ^ 10 ≤ 2 * (x + 1) ^ 10 := by
        have := pow_le_pow_left₀ hx0.le (by linarith : x ≤ x + 1) 10
        linarith
      have h4 : Cc ≤ 16 * (x + 1) ^ 14 := by
        calc
          Cc ≤ (2 * (x + 1) ^ 3) * (4 * (x + 1)) * (2 * (x + 1) ^ 10) := by
            rw [hCcdef]
            apply mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3
              (by positivity) (by positivity)
          _ = 16 * (x + 1) ^ 14 := by ring
      have h5 : (32 : ℝ) ≤ (x + 1) ^ 5 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (2 : ℝ) ≤ x + 1) 5
        norm_num at this
        linarith
      have h6 : (1 : ℝ) ≤ (x + 1) ^ 14 := one_le_pow₀ (by linarith)
      calc
        Cc + 1 ≤ 16 * (x + 1) ^ 14 + (x + 1) ^ 14 := by linarith
        _ = 17 * (x + 1) ^ 14 := by ring
        _ ≤ (x + 1) ^ 5 * (x + 1) ^ 14 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (x + 1) ^ 19 := by ring
    have hlogC : Real.log (Cc + 1) ≤ 38 * x ^ δ / δ := by
      have h1 : Real.log (Cc + 1) ≤ 19 * Real.log (x + 1) := by
        have := Real.log_le_log (by positivity) hCc
        rwa [Real.log_pow] at this
      have h2 : Real.log (x + 1) ≤ (x + 1) ^ δ / δ :=
        Real.log_le_rpow_div (by positivity) hδ
      have h3 : (x + 1) ^ δ ≤ (2 * x) ^ δ :=
        Real.rpow_le_rpow (by positivity) (by linarith) hδ.le
      have h4 : (2 * x) ^ δ ≤ 2 * x ^ δ := by
        rw [Real.mul_rpow (by norm_num) hx0.le]
        have : (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        rw [Real.rpow_one] at this
        exact mul_le_mul_of_nonneg_right this (by positivity)
      have h5 : (x + 1) ^ δ / δ ≤ 2 * x ^ δ / δ :=
        div_le_div_of_nonneg_right (h3.trans h4) hδ.le
      calc
        Real.log (Cc + 1) ≤ 19 * ((x + 1) ^ δ / δ) := by
          have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 19)
          linarith
        _ ≤ 19 * (2 * x ^ δ / δ) := mul_le_mul_of_nonneg_left h5 (by norm_num)
        _ = 38 * x ^ δ / δ := by ring
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have hlog2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
    -- RHS lower bound
    have hR : (2 / 100 : ℝ) * x ^ (299 * δ) * x ≤ (2 / 100 : ℝ) * x ^ (-δ) * k * x := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hak (by norm_num : (0 : ℝ) ≤ 2 / 100)) hx0.le
      calc
        (2 / 100 : ℝ) * x ^ (299 * δ) * x ≤ (2 / 100 : ℝ) * (x ^ (-δ) * k) * x := this
        _ = (2 / 100 : ℝ) * x ^ (-δ) * k * x := by ring
    -- term 1
    have ht1 : x * Real.log 2 ≤ (2 / 300 : ℝ) * x ^ (299 * δ) * x := by
      calc
        x * Real.log 2 ≤ x * 1 := mul_le_mul_of_nonneg_left hlog2.le hx0.le
        _ = (2 / 300 : ℝ) * 150 * x := by ring
        _ ≤ (2 / 300 : ℝ) * x ^ (299 * δ) * x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h150 (by norm_num)) hx0.le
    -- term 2
    have ht2 : 2 * k * (m + ((Nat.log 2 n : ℝ) + 1)) ≤ (2 / 300 : ℝ) * x ^ (299 * δ) * x := by
      have h1 : m + ((Nat.log 2 n : ℝ) + 1) ≤ 2 * x ^ (200 * δ) := by linarith
      have h2 : 2 * k * (m + ((Nat.log 2 n : ℝ) + 1)) ≤
          2 * (2 * x ^ (300 * δ)) * (2 * x ^ (200 * δ)) := by
        apply mul_le_mul (by linarith) h1 (by positivity) (by positivity)
      have h3 : x ^ (300 * δ) * x ^ (200 * δ) = x ^ (201 * δ) * x ^ (299 * δ) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
      have hlin' : 1200 * x ^ (201 * δ) ≤ x := hlin
      have h4 : 8 * (x ^ (201 * δ) * x ^ (299 * δ)) ≤ (2 / 300 : ℝ) * x ^ (299 * δ) * x := by
        have hp : 0 ≤ x ^ (299 * δ) := by positivity
        linarith [mul_le_mul_of_nonneg_right hlin' hp]
      calc
        2 * k * (m + ((Nat.log 2 n : ℝ) + 1)) ≤ 2 * (2 * x ^ (300 * δ)) * (2 * x ^ (200 * δ)) := h2
        _ = 8 * (x ^ (300 * δ) * x ^ (200 * δ)) := by ring
        _ = 8 * (x ^ (201 * δ) * x ^ (299 * δ)) := by rw [h3]
        _ ≤ _ := h4
    -- term 3
    have ht3 : x * ((((p10_1kHeightCount n δ + min (p10_1kSpecialCount n δ) n : ℕ) : ℝ)) *
        Real.log (Cc + 1)) ≤ (2 / 300 : ℝ) * x ^ (299 * δ) * x := by
      have hcast : (((p10_1kHeightCount n δ + min (p10_1kSpecialCount n δ) n : ℕ) : ℝ)) =
          T + m := by
        rw [hTdef, hmdef]; push_cast; ring
      rw [hcast]
      have hTm : T + m ≤ 3 * x ^ (200 * δ) := by linarith
      have hlogC0 : 0 ≤ Real.log (Cc + 1) := Real.log_nonneg (by linarith)
      have h1 : (T + m) * Real.log (Cc + 1) ≤ 3 * x ^ (200 * δ) * (38 * x ^ δ / δ) :=
        mul_le_mul hTm hlogC (by positivity) (by positivity)
      have h2 : x ^ (200 * δ) * x ^ δ = x ^ (201 * δ) := by
        rw [← Real.rpow_add hx0]; ring_nf
      have h3 : 3 * x ^ (200 * δ) * (38 * x ^ δ / δ) = (114 / δ) * x ^ (201 * δ) := by
        rw [← h2]; field_simp; ring
      have hpow' : 17100 / δ * x ^ (201 * δ) ≤ x ^ (299 * δ) := hpow
      have h4 : (114 / δ) * x ^ (201 * δ) ≤ (2 / 300 : ℝ) * x ^ (299 * δ) := by
        have : (114 / δ) * x ^ (201 * δ) = (2 / 300 : ℝ) * (17100 / δ * x ^ (201 * δ)) := by
          field_simp; ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hpow' (by norm_num)
      calc
        x * ((T + m) * Real.log (Cc + 1)) ≤ x * ((114 / δ) * x ^ (201 * δ)) := by
          rw [← h3]; exact mul_le_mul_of_nonneg_left h1 hx0.le
        _ ≤ x * ((2 / 300 : ℝ) * x ^ (299 * δ)) := mul_le_mul_of_nonneg_left h4 hx0.le
        _ = (2 / 300 : ℝ) * x ^ (299 * δ) * x := by ring
    linarith

end HypercubeRamsey.Lane_opus_s10_d6
