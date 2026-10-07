import Mathlib

/-!
# Lemma 3.5: scattered moments

Source: `sections/03-…tex`, Lemma 3.5 and its proof. The success event is `succ`; the comparison means are
`d`; `near v` is the near set of `v` (containing `v`), of size at most `f |U|`.
-/

namespace HypercubeRamsey

open Classical

private def scatteredRemovedAt {U : Type*} [DecidableEq U] {m : ℕ}
    (near : U → Finset U) (s : Fin m → U) (i : Fin m) : Prop :=
  ∃ j, j < i ∧ s i ∈ near (s j)

private noncomputable def scatteredWeight {U : Type*} [DecidableEq U] {m : ℕ}
    (near : U → Finset U) (s : Fin m → U) (L : ℝ) (d : U → ℝ) : ℝ := by
  classical
  exact ∏ i, if scatteredRemovedAt near s i then L else d (s i)

private def scatteredClose {U : Type*} [DecidableEq U] {m : ℕ}
    (near : U → Finset U) (s : Fin m → U) (v : U) : Prop :=
  ∃ j : Fin m, v ∈ near (s j)

private lemma scattered_next_sum_bound {U : Type*} [Fintype U] [DecidableEq U]
    {m : ℕ} (near : U → Finset U) (s : Fin m → U) (f L : ℝ) (hL : 0 ≤ L)
    (hnear : ∀ v, ((near v).card : ℝ) ≤ f * Fintype.card U)
    (d : U → ℝ) (hd : ∀ v, 0 ≤ d v) :
    ∑ v, (if scatteredClose near s v then L else d v) ≤
      (∑ v, d v) + (m : ℝ) * f * Fintype.card U * L := by
  classical
  let A : Finset U := Finset.univ.filter (scatteredClose near s)
  have hsub : A ⊆ Finset.univ.biUnion (fun j : Fin m => near (s j)) := by
    intro v hv
    rcases (Finset.mem_filter.mp hv).2 with ⟨j, hj⟩
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩
  have hcard : (A.card : ℝ) ≤ (m : ℝ) * f * Fintype.card U := by
    calc
      (A.card : ℝ) ≤ ((Finset.univ.biUnion (fun j : Fin m => near (s j))).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ ∑ j : Fin m, ((near (s j)).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ)
          (t := fun j : Fin m => near (s j)))
      _ ≤ ∑ j : Fin m, f * Fintype.card U := Finset.sum_le_sum fun j _ => hnear (s j)
      _ = (m : ℝ) * f * Fintype.card U := by simp [mul_assoc]
  have hbad : (∑ v ∈ A, L) ≤ (m : ℝ) * f * Fintype.card U * L := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard hL
  have hgood : (∑ v ∈ Finset.univ with ¬ scatteredClose near s v, d v) ≤ ∑ v, d v := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro v _ _
    exact hd v
  have hbadEq : (∑ v ∈ A, L) =
      ∑ v ∈ Finset.univ with scatteredClose near s v,
        (if scatteredClose near s v then L else d v) := by
    change (∑ v ∈ Finset.univ.filter (scatteredClose near s), L) = _
    apply Finset.sum_congr rfl
    intro v hv
    simp [(Finset.mem_filter.mp hv).2]
  have hgoodEq :
      (∑ v ∈ Finset.univ with ¬ scatteredClose near s v,
        (if scatteredClose near s v then L else d v)) =
      ∑ v ∈ Finset.univ with ¬ scatteredClose near s v, d v := by
    apply Finset.sum_congr rfl
    intro v hv
    simp [(Finset.mem_filter.mp hv).2]
  calc
    ∑ v, (if scatteredClose near s v then L else d v) =
        (∑ v ∈ A, L) + ∑ v ∈ Finset.univ with ¬ scatteredClose near s v, d v := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := scatteredClose near s) (f := fun v => if scatteredClose near s v then L else d v)]
      rw [hbadEq, hgoodEq]
    _ ≤ (m : ℝ) * f * Fintype.card U * L + ∑ v, d v := add_le_add hbad hgood
    _ = (∑ v, d v) + (m : ℝ) * f * Fintype.card U * L := by ring

private lemma scatteredRemovedAt_snoc_castSucc {U : Type*} [DecidableEq U] {m : ℕ}
    (near : U → Finset U) (s : Fin m → U) (v : U) (i : Fin m) :
    scatteredRemovedAt near (Fin.snoc s v) i.castSucc ↔ scatteredRemovedAt near s i := by
  classical
  unfold scatteredRemovedAt
  constructor
  · rintro ⟨j, hji, hmem⟩
    have hjne : j ≠ Fin.last m := by
      intro heq
      subst j
      exact (not_lt_of_ge (Fin.castSucc_lt_last i).le) hji
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hjne
    refine ⟨j, ?_, ?_⟩
    · simpa using hji
    · simpa using hmem
  · rintro ⟨j, hji, hmem⟩
    exact ⟨j.castSucc, by simpa using hji, by simpa using hmem⟩

private lemma scatteredRemovedAt_snoc_last {U : Type*} [DecidableEq U] {m : ℕ}
    (near : U → Finset U) (s : Fin m → U) (v : U) :
    scatteredRemovedAt near (Fin.snoc s v) (Fin.last m) ↔ scatteredClose near s v := by
  classical
  unfold scatteredRemovedAt scatteredClose
  constructor
  · rintro ⟨j, hj, hmem⟩
    have hjne : j ≠ Fin.last m := by
      intro heq
      subst j
      exact (lt_irrefl _ hj)
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hjne
    exact ⟨j, by simpa using hmem⟩
  · rintro ⟨j, hmem⟩
    exact ⟨j.castSucc, Fin.castSucc_lt_last j, by simpa using hmem⟩

private lemma scatteredWeight_snoc {U : Type*} [DecidableEq U] {m : ℕ}
    (near : U → Finset U) (s : Fin m → U) (v : U) (L : ℝ) (d : U → ℝ) :
    scatteredWeight near (Fin.snoc s v) L d =
      scatteredWeight near s L d * (if scatteredClose near s v then L else d v) := by
  classical
  unfold scatteredWeight
  rw [Fin.prod_univ_castSucc]
  simp only [scatteredRemovedAt_snoc_castSucc, scatteredRemovedAt_snoc_last,
    Fin.snoc_castSucc, Fin.snoc_last]

private lemma scattered_weight_sum_bound {U : Type*} [Fintype U] [DecidableEq U]
    [Nonempty U] (near : U → Finset U) (hself : ∀ v, v ∈ near v)
    (f : ℝ) (hnear : ∀ v, ((near v).card : ℝ) ≤ f * Fintype.card U)
    (d : U → ℝ) (hd : ∀ v, 0 ≤ d v) (L : ℝ) (hL : 0 ≤ L)
    (n : ℕ) : ∀ m ≤ n,
      (∑ s : Fin m → U, scatteredWeight near s L d) ≤
        ((∑ v, d v) + (n : ℝ) * f * Fintype.card U * L) ^ m := by
  classical
  intro m hm
  induction m with
  | zero => simp [scatteredWeight]
  | succ m ih =>
    let C : ℝ := (∑ v, d v) + (n : ℝ) * f * Fintype.card U * L
    have hm' : m ≤ n := Nat.le_of_succ_le hm
    have hN : 0 < (Fintype.card U : ℝ) := Nat.cast_pos.mpr (Fintype.card_pos)
    have hf : 0 ≤ f := by
      obtain ⟨u⟩ := ‹Nonempty U›
      have hu : (1 : ℝ) ≤ (near u).card := by
        exact_mod_cast Finset.one_le_card.mpr ⟨u, hself u⟩
      by_contra hnot
      have hfn : f < 0 := lt_of_not_ge hnot
      have hmul : f * Fintype.card U ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hfn.le hN.le
      linarith [hnear u]
    have hcoef : (m : ℝ) * f * Fintype.card U * L ≤
        (n : ℝ) * f * Fintype.card U * L := by
      have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm'
      have hfnN : 0 ≤ f * Fintype.card U := mul_nonneg hf hN.le
      have hmfn : (m : ℝ) * f ≤ (n : ℝ) * f := mul_le_mul_of_nonneg_right hmn hf
      have hmfnN : (m : ℝ) * f * Fintype.card U ≤
          (n : ℝ) * f * Fintype.card U := mul_le_mul_of_nonneg_right hmfn hN.le
      exact mul_le_mul_of_nonneg_right hmfnN hL
    have hD : 0 ≤ (∑ v, d v) := Finset.sum_nonneg fun v _ => hd v
    have hC : 0 ≤ C := add_nonneg hD (by positivity)
    have hlocal (t : Fin m → U) :
        ∑ v : U, scatteredWeight near (Fin.snoc t v) L d ≤
          scatteredWeight near t L d * C := by
      simp_rw [scatteredWeight_snoc]
      have hwt : 0 ≤ scatteredWeight near t L d := by
        unfold scatteredWeight
        apply Finset.prod_nonneg
        intro i hi
        by_cases h : scatteredRemovedAt near t i
        · simp [h, hL]
        · simp [h, hd (t i)]
      calc
        ∑ v : U, scatteredWeight near t L d *
            (if scatteredClose near t v then L else d v) =
            scatteredWeight near t L d *
              ∑ v : U, (if scatteredClose near t v then L else d v) := by
                rw [Finset.mul_sum]
        _ ≤ scatteredWeight near t L d * C :=
          mul_le_mul_of_nonneg_left
            (le_trans (scattered_next_sum_bound near t f L hL hnear d hd) (by
              calc
                (∑ v, d v) + (m : ℝ) * f * Fintype.card U * L =
                    (m : ℝ) * f * Fintype.card U * L + ∑ v, d v := by ring
                _ ≤ (n : ℝ) * f * Fintype.card U * L + ∑ v, d v :=
                    by linarith [hcoef]
                _ = (∑ v, d v) + (n : ℝ) * f * Fintype.card U * L := by ring)) hwt
    have hsum :
        (∑ s : Fin (m + 1) → U, scatteredWeight near s L d) =
          ∑ p : U × (Fin m → U), scatteredWeight near (Fin.snoc p.2 p.1) L d := by
      symm
      exact Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (m + 1) => U))
        (fun p => scatteredWeight near (Fin.snoc p.2 p.1) L d)
        (fun s => scatteredWeight near s L d) (by intro p; rfl)
    rw [hsum, Fintype.sum_prod_type]
    calc
      ∑ v : U, ∑ t : Fin m → U, scatteredWeight near (Fin.snoc t v) L d =
          ∑ t : Fin m → U, ∑ v : U, scatteredWeight near (Fin.snoc t v) L d := by
            rw [Finset.sum_comm]
      _ ≤ ∑ t : Fin m → U, scatteredWeight near t L d * C :=
            Finset.sum_le_sum fun t _ => hlocal t
      _ = (∑ t : Fin m → U, scatteredWeight near t L d) * C := by rw [Finset.sum_mul]
      _ ≤ C ^ m * C := mul_le_mul_of_nonneg_right (ih hm') hC
      _ = C ^ (m + 1) := by rw [pow_succ]

theorem scattered_moments {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (succ : Finset Ω) (Z : U → Ω → ℝ) (hZ0 : ∀ v ω, 0 ≤ Z v ω) (L : ℝ) (hL : 0 ≤ L)
    (hZL : ∀ v, ∀ ω ∈ succ, Z v ω ≤ L)
    (near : U → Finset U) (hself : ∀ v, v ∈ near v) (f : ℝ)
    (hnear : ∀ v, ((near v).card : ℝ) ≤ f * Fintype.card U)
    (n : ℕ) (K : ℝ) (hK : 1 ≤ K) (d : U → ℝ) (hd : ∀ v, 0 ≤ d v)
    (hjoint : ∀ (m : ℕ), m ≤ n → ∀ s : Fin m → U,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
        ∑ ω ∈ succ, w ω * ∏ i, Z (s i) ω ≤ K ^ m * ∏ i, d (s i)) :
    ∑ ω ∈ succ, w ω * ((Fintype.card U : ℝ)⁻¹ * ∑ v, Z v ω) ^ n ≤
      K ^ n * ((Fintype.card U : ℝ)⁻¹ * ∑ v, d v + n * f * L) ^ n := by
  classical
  let N : ℝ := Fintype.card U
  let C : ℝ := (∑ v, d v) + (n : ℝ) * f * N * L
  let a : ℝ := N⁻¹
  have hN : 0 < N := by dsimp [N]; exact Nat.cast_pos.mpr Fintype.card_pos
  have hNne : N ≠ 0 := hN.ne'
  have hweight := scattered_weight_sum_bound near hself f hnear d hd L hL n n (le_rfl)
  have htuple (s : Fin n → U) :
      (∑ ω ∈ succ, w ω * ∏ i, Z (s i) ω) ≤ K ^ n * scatteredWeight near s L d := by
    let G : Finset (Fin n) := Finset.univ.filter
      (fun i => ¬ scatteredRemovedAt near s i)
    let m : ℕ := G.card
    let e : Fin m ↪o Fin n := G.orderEmbOfFin rfl
    let t : Fin m → U := fun i => s (e i)
    have hm : m ≤ n := by
      simpa [m] using (Finset.card_le_univ G)
    have hsep : ∀ i j : Fin m, j < i → t i ∉ near (t j) := by
      intro i j hji hmem
      have hiG : e i ∈ G := Finset.orderEmbOfFin_mem G rfl i
      have hgood : ¬ scatteredRemovedAt near s (e i) := by
        simpa [G] using (Finset.mem_filter.mp hiG).2
      apply hgood
      exact ⟨e j, e.strictMono hji, hmem⟩
    have hprodZ (ω : Ω) : (∏ i : Fin m, Z (t i) ω) =
        ∏ i ∈ G, Z (s i) ω := by
      change (∏ i ∈ (Finset.univ : Finset (Fin m)), Z (s (e i)) ω) = _
      refine Finset.prod_bij (fun i _ => e i) ?_ ?_ ?_ ?_
      · intro i hi
        exact Finset.orderEmbOfFin_mem G rfl i
      · intro i hi j hj heq
        exact e.injective heq
      · intro j hj
        obtain ⟨i, hi⟩ := (G.orderIsoOfFin rfl).surjective ⟨j, hj⟩
        refine ⟨i, Finset.mem_univ _, ?_⟩
        have h := congrArg Subtype.val hi
        change G.orderEmbOfFin rfl i = j
        rw [← Finset.coe_orderIsoOfFin_apply]
        exact h
      · intro i hi
        rfl
    have hprodD : (∏ i : Fin m, d (t i)) = ∏ i ∈ G, d (s i) := by
      change (∏ i ∈ (Finset.univ : Finset (Fin m)), d (s (e i))) = _
      refine Finset.prod_bij (fun i _ => e i) ?_ ?_ ?_ ?_
      · intro i hi
        exact Finset.orderEmbOfFin_mem G rfl i
      · intro i hi j hj heq
        exact e.injective heq
      · intro j hj
        obtain ⟨i, hi⟩ := (G.orderIsoOfFin rfl).surjective ⟨j, hj⟩
        refine ⟨i, Finset.mem_univ _, ?_⟩
        have h := congrArg Subtype.val hi
        change G.orderEmbOfFin rfl i = j
        rw [← Finset.coe_orderIsoOfFin_apply]
        exact h
      · intro i hi
        rfl
    have hcomp := hjoint m hm t hsep
    have hcomp' :
        (∑ ω ∈ succ, w ω * ∏ i ∈ G, Z (s i) ω) ≤
          K ^ m * ∏ i ∈ G, d (s i) := by
      simpa only [hprodZ, hprodD] using hcomp
    let bad : Finset (Fin n) := Finset.univ.filter (scatteredRemovedAt near s)
    have hsplit (ω : Ω) :
        (∏ i, Z (s i) ω) =
          (∏ i ∈ bad, Z (s i) ω) * (∏ i ∈ G, Z (s i) ω) := by
      dsimp [bad, G]
      simpa using (Finset.prod_filter_mul_prod_filter_not Finset.univ
        (scatteredRemovedAt near s) (fun i => Z (s i) ω)).symm
    have hbad (ω : Ω) (hω : ω ∈ succ) :
        (∏ i ∈ bad, Z (s i) ω) ≤ ∏ i ∈ bad, L := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact hZ0 (s i) ω
      · intro i hi
        exact hZL (s i) ω hω
    have hgood0 (ω : Ω) : 0 ≤ ∏ i ∈ G, Z (s i) ω := by
      apply Finset.prod_nonneg
      intro i hi
      exact hZ0 (s i) ω
    have hLbad0 : 0 ≤ ∏ i ∈ bad, L := by
      apply Finset.prod_nonneg
      intro i hi
      exact hL
    have hsum :
        (∑ ω ∈ succ, w ω * ∏ i, Z (s i) ω) ≤
          (∏ i ∈ bad, L) * (∑ ω ∈ succ, w ω * ∏ i ∈ G, Z (s i) ω) := by
      calc
        _ ≤ ∑ ω ∈ succ, w ω *
            ((∏ i ∈ bad, L) * (∏ i ∈ G, Z (s i) ω)) := by
              apply Finset.sum_le_sum
              intro ω hω
              rw [hsplit ω]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (hbad ω hω) (hgood0 ω)) (hw ω)
        _ = (∏ i ∈ bad, L) *
            (∑ ω ∈ succ, w ω * ∏ i ∈ G, Z (s i) ω) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ω hω
              ring
    have hsum' :
        (∑ ω ∈ succ, w ω * ∏ i, Z (s i) ω) ≤
          (∏ i ∈ bad, L) * (K ^ m * ∏ i ∈ G, d (s i)) :=
      le_trans hsum (mul_le_mul_of_nonneg_left hcomp' hLbad0)
    have hKm : K ^ m ≤ K ^ n := by
      exact pow_le_pow_right₀ hK hm
    have hDgood0 : 0 ≤ ∏ i ∈ G, d (s i) := by
      apply Finset.prod_nonneg
      intro i hi
      exact hd (s i)
    have hKweight :
        (∏ i ∈ bad, L) * (K ^ m * ∏ i ∈ G, d (s i)) ≤
          K ^ n * scatteredWeight near s L d := by
      have hfactor :
          (∏ i ∈ bad, L) * ∏ i ∈ G, d (s i) = scatteredWeight near s L d := by
        unfold scatteredWeight
        have hb : (∏ i ∈ bad, L) =
            ∏ i ∈ Finset.univ with scatteredRemovedAt near s i,
              (if scatteredRemovedAt near s i then L else d (s i)) := by
          apply Finset.prod_congr
          · simp [bad]
          · intro i hi
            simp [(Finset.mem_filter.mp hi).2]
        have hg : (∏ i ∈ G, d (s i)) =
            ∏ i ∈ Finset.univ with ¬ scatteredRemovedAt near s i,
              (if scatteredRemovedAt near s i then L else d (s i)) := by
          apply Finset.prod_congr
          · simp [G]
          · intro i hi
            simp [(Finset.mem_filter.mp hi).2]
        rw [hb, hg]
        simpa using (Finset.prod_filter_mul_prod_filter_not Finset.univ
          (scatteredRemovedAt near s)
          (fun i => if scatteredRemovedAt near s i then L else d (s i)))

      calc
        (∏ i ∈ bad, L) * (K ^ m * ∏ i ∈ G, d (s i)) =
            K ^ m * ((∏ i ∈ bad, L) * ∏ i ∈ G, d (s i)) := by ring
        _ ≤ K ^ n * ((∏ i ∈ bad, L) * ∏ i ∈ G, d (s i)) :=
            mul_le_mul_of_nonneg_right hKm (mul_nonneg hLbad0 hDgood0)
        _ = K ^ n * scatteredWeight near s L d := by rw [hfactor]
    exact le_trans hsum' hKweight
  have hmoment_expansion :
      (∑ ω ∈ succ, w ω * (a * ∑ v, Z v ω) ^ n) =
        a ^ n * ∑ s : Fin n → U, ∑ ω ∈ succ, w ω * ∏ i, Z (s i) ω := by
    calc
      _ = ∑ ω ∈ succ, ∑ s : Fin n → U, a ^ n * (w ω * ∏ i, Z (s i) ω) := by
        apply Finset.sum_congr rfl
        intro ω hω
        rw [mul_pow, Fintype.sum_pow]
        calc
          w ω * (a ^ n * ∑ s : Fin n → U, ∏ i, Z (s i) ω) =
              (w ω * a ^ n) * ∑ s : Fin n → U, ∏ i, Z (s i) ω := by ring
          _ = ∑ s : Fin n → U, a ^ n * (w ω * ∏ i, Z (s i) ω) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s hs
              ring
      _ = ∑ s : Fin n → U, ∑ ω ∈ succ, a ^ n * (w ω * ∏ i, Z (s i) ω) := by
        rw [Finset.sum_comm]
      _ = a ^ n * ∑ s : Fin n → U, ∑ ω ∈ succ, w ω * ∏ i, Z (s i) ω := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mul_sum]
  have hsum_bound :
      (∑ s : Fin n → U, ∑ ω ∈ succ, w ω * ∏ i, Z (s i) ω) ≤ K ^ n * C ^ n := by
    calc
      _ ≤ ∑ s : Fin n → U, K ^ n * scatteredWeight near s L d :=
        Finset.sum_le_sum fun s _ => htuple s
      _ = K ^ n * ∑ s : Fin n → U, scatteredWeight near s L d := by
        rw [Finset.mul_sum]
      _ ≤ K ^ n * C ^ n := by
        dsimp [C, N]
        exact mul_le_mul_of_nonneg_left hweight (by positivity [hK])
  have hscaled : a ^ n * (K ^ n * C ^ n) = K ^ n * (a * C) ^ n := by
    rw [mul_pow]
    ring
  have hscaleC : a * C = (Fintype.card U : ℝ)⁻¹ * ∑ v, d v + n * f * L := by
    dsimp [a, C, N]
    field_simp [hNne]
  rw [show (∑ ω ∈ succ, w ω * ((Fintype.card U : ℝ)⁻¹ * ∑ v, Z v ω) ^ n) =
      ∑ ω ∈ succ, w ω * (a * ∑ v, Z v ω) ^ n by
        apply Finset.sum_congr rfl
        intro ω hω
        simp [a, N]]
  rw [hmoment_expansion]
  calc
    a ^ n * ∑ s : Fin n → U, ∑ ω ∈ succ, w ω * ∏ i, Z (s i) ω ≤
        a ^ n * (K ^ n * C ^ n) := mul_le_mul_of_nonneg_left hsum_bound (by positivity [hN])
    _ = K ^ n * (a * C) ^ n := hscaled
    _ = K ^ n * ((Fintype.card U : ℝ)⁻¹ * ∑ v, d v + n * f * L) ^ n := by rw [hscaleC]

end HypercubeRamsey
