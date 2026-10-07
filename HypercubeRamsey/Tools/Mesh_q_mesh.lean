import Mathlib

namespace HypercubeRamsey.Lane_q_mesh

open scoped BigOperators

def affineEval {D m : ℕ} (a : Fin m → Fin D → ℝ)
    (e : Fin (D + 2) ↪ Fin m) :
    (Fin (D + 1) → ℝ) →ₗ[ℝ] (Fin (D + 2) → ℝ) where
  toFun b k := b (Fin.last D) + ∑ j : Fin D, b (Fin.castSucc j) * a (e k) j
  map_add' b c := by
    ext k
    simp only [Pi.add_apply, Finset.sum_add_distrib, add_mul]
    ring
  map_smul' r b := by
    ext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add, Finset.mul_sum]
    ring_nf

def restrict {D m : ℕ} (e : Fin (D + 2) ↪ Fin m) :
    (Fin m → ℝ) →ₗ[ℝ] (Fin (D + 2) → ℝ) where
  toFun f k := f (e k)
  map_add' f g := by ext k; rfl
  map_smul' r f := by ext k; rfl

def badSubspace {D m : ℕ} (a : Fin m → Fin D → ℝ)
    (e : Fin (D + 2) ↪ Fin m) : Submodule ℝ (Fin m → ℝ) :=
  Submodule.comap (restrict e) (affineEval a e).range

theorem affineEval_range_ne_top {D m : ℕ} (a : Fin m → Fin D → ℝ)
    (e : Fin (D + 2) ↪ Fin m) : (affineEval a e).range ≠ ⊤ := by
  let A := affineEval a e
  have hle : Module.finrank ℝ A.range ≤ D + 1 := by
    calc
      Module.finrank ℝ A.range ≤ Module.finrank ℝ (Fin (D + 1) → ℝ) := A.finrank_range_le
      _ = D + 1 := by simp
  have hdim : Module.finrank ℝ (Fin (D + 2) → ℝ) = D + 2 := by
    simp
  have hlt : Module.finrank ℝ A.range <
      Module.finrank ℝ (Fin (D + 2) → ℝ) := by
    rw [hdim]
    omega
  have hlt' : A.range < ⊤ := Submodule.lt_top_of_finrank_lt_finrank hlt
  exact ne_of_lt hlt'

theorem restrict_surjective {D m : ℕ} (e : Fin (D + 2) ↪ Fin m) :
    Function.Surjective (restrict e) := by
  intro y
  refine ⟨Function.extend e y 0, ?_⟩
  ext k
  simp [restrict, e.injective.extend_apply]

theorem badSubspace_ne_top {D m : ℕ} (a : Fin m → Fin D → ℝ)
    (e : Fin (D + 2) ↪ Fin m) : badSubspace a e ≠ ⊤ := by
  intro htop
  have hrange : (affineEval a e).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro y
    obtain ⟨q, hq⟩ := restrict_surjective e y
    have hqmem : q ∈ badSubspace a e := by rw [htop]; exact Submodule.mem_top
    change restrict e q ∈ (affineEval a e).range at hqmem
    rw [hq] at hqmem
    exact hqmem
  exact affineEval_range_ne_top a e hrange

theorem exists_vector_avoiding_badSubspaces {D m : ℕ} (a : Fin m → Fin D → ℝ) :
    ∃ v : Fin m → ℝ, ∀ e : Fin (D + 2) ↪ Fin m, v ∉ badSubspace a e := by
  let S : Finset (Submodule ℝ (Fin m → ℝ)) :=
    Finset.univ.image (fun e : Fin (D + 2) ↪ Fin m => badSubspace a e)
  have htop : (⊤ : Submodule ℝ (Fin m → ℝ)) ∉ S := by
    intro h
    rcases Finset.mem_image.mp h with ⟨e, -, he⟩
    exact badSubspace_ne_top a e he
  have hcover : (⋃ B ∈ S, (B : Set (Fin m → ℝ))) ≠ Set.univ :=
    Subspace.biUnion_ne_univ_of_top_notMem htop
  have hex : ∃ v : Fin m → ℝ, v ∉ ⋃ B ∈ S, (B : Set (Fin m → ℝ)) := by
    by_contra h
    push Not at h
    apply hcover
    ext v
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    simpa only [Set.mem_iUnion] using h v
  obtain ⟨v, hv⟩ := hex
  refine ⟨v, fun e hve => hv ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨badSubspace a e, ?_⟩
  apply Set.mem_iUnion.mpr
  exact ⟨Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩, hve⟩

theorem exists_small_avoiding_badSubspaces {D m : ℕ} (a : Fin m → Fin D → ℝ)
    (q₀ : Fin m → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Fin m → ℝ, (∀ e : Fin (D + 2) ↪ Fin m, q ∉ badSubspace a e) ∧
      ∀ i, |q i - q₀ i| < ε := by
  obtain ⟨v, hv⟩ := exists_vector_avoiding_badSubspaces a
  let B : ℝ := 1 + ∑ i : Fin m, |v i|
  have hB : 0 < B := by
    dsimp [B]
    positivity
  let ε' := ε / B
  have hε' : 0 < ε' := div_pos hε hB
  let T : (Fin (D + 2) ↪ Fin m) → Set ℝ :=
    fun e => {t | q₀ + t • v ∈ badSubspace a e}
  have hT : ∀ e, (T e).Finite := by
    intro e
    have hunique : ∀ s, s ∈ T e → ∀ t, t ∈ T e → s = t := by
      intro s hs t ht
      by_contra hst
      have hvsub : (s - t) • v ∈ badSubspace a e := by
        simpa [sub_smul] using (badSubspace a e).sub_mem hs ht
      have hvbad : v ∈ badSubspace a e := by
        have hscl := (badSubspace a e).smul_mem ((s - t)⁻¹) hvsub
        have hnz : s - t ≠ 0 := sub_ne_zero.mpr hst
        simpa [smul_smul, hnz] using hscl
      exact hv e hvbad
    by_cases hne : (T e).Nonempty
    · obtain ⟨s, hs⟩ := hne
      refine Set.Finite.subset (Set.finite_singleton s) ?_
      intro t ht
      exact (hunique s hs t ht).symm
    · refine Set.Finite.subset (Set.finite_singleton (0 : ℝ)) ?_
      intro t ht
      exact False.elim (hne ⟨t, ht⟩)
  have htimes : (⋃ e, T e).Finite := Set.finite_iUnion hT
  obtain ⟨t, ht, htnot⟩ := (Set.Ioo_infinite hε').exists_notMem_finite htimes
  have ht0 : 0 < t := ht.1
  have htε : t < ε' := ht.2
  have hsum : ∀ i : Fin m, |v i| ≤ ∑ j : Fin m, |v j| := by
    intro i
    exact Finset.single_le_sum (f := fun j : Fin m => |v j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hcoord : ∀ i : Fin m, |t * v i| < ε := by
    intro i
    have hiv : |v i| < B := by dsimp [B]; linarith [hsum i]
    have hmul : t * |v i| < ε := by
      calc
        t * |v i| < t * B := mul_lt_mul_of_pos_left hiv ht0
        _ < ε := (lt_div_iff₀ hB).mp htε
    simpa [abs_mul, abs_of_pos ht0] using hmul
  refine ⟨q₀ + t • v, ?_, ?_⟩
  · intro e hq
    apply htnot
    exact Set.mem_iUnion.mpr ⟨e, hq⟩
  · intro i
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hcoord i

def sqNorm {D : ℕ} (x : Fin D → ℝ) : ℝ := ∑ j, (x j) ^ 2

def sqDist {D : ℕ} (x y : Fin D → ℝ) : ℝ := ∑ j, (x j - y j) ^ 2

theorem sum_sq_sub_eq {D : ℕ} (x y : Fin D → ℝ) :
    ∑ j, (x j - y j) ^ 2 = sqNorm x - 2 * ∑ j, x j * y j + sqNorm y := by
  calc
    ∑ j, (x j - y j) ^ 2 = ∑ j, ((x j) ^ 2 - 2 * (x j * y j) + (y j) ^ 2) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ j, (x j) ^ 2) - (∑ j, 2 * (x j * y j)) + (∑ j, (y j) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = sqNorm x - 2 * ∑ j, x j * y j + sqNorm y := by
      dsimp [sqNorm]
      rw [Finset.mul_sum]

theorem sum_sq_le_of_abs_le {D : ℕ} (x : Fin D → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hx : ∀ j, |x j| ≤ η) : ∑ j, (x j) ^ 2 ≤ (D : ℝ) * η ^ 2 := by
  calc
    ∑ j, (x j) ^ 2 ≤ ∑ j, η ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (x j)) hη).2 (hx j)
    _ = (D : ℝ) * η ^ 2 := by simp

def power {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (i : Fin m) (p : Fin D → ℝ) : ℝ := q i - 2 * ∑ j, p j * a i j

theorem power_sqDist_identity {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (i : Fin m) (p : Fin D → ℝ) :
    power a q i p + sqNorm p = sqDist p (a i) + (q i - sqNorm (a i)) := by
  rw [power, sqDist, sum_sq_sub_eq]
  dsimp [sqNorm]
  ring

def powerMin {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (i₀ : Fin m) (p : Fin D → ℝ) : ℝ :=
  letI : Nonempty (Fin m) := ⟨i₀⟩
  Finset.univ.inf' Finset.univ_nonempty (fun i => power a q i p)

def powerMax {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (i₀ : Fin m) (p : Fin D → ℝ) : ℝ :=
  letI : Nonempty (Fin m) := ⟨i₀⟩
  Finset.univ.sup' Finset.univ_nonempty (fun i => power a q i p)

theorem powerMin_le {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (i₀ : Fin m) (p : Fin D → ℝ) (i : Fin m) : powerMin a q i₀ p ≤ power a q i p := by
  unfold powerMin
  letI : Nonempty (Fin m) := ⟨i₀⟩
  exact Finset.inf'_le (f := fun j => power a q j p) (Finset.mem_univ i)

theorem power_le_max {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (i₀ : Fin m) (p : Fin D → ℝ) (i : Fin m) : power a q i p ≤ powerMax a q i₀ p := by
  unfold powerMax
  letI : Nonempty (Fin m) := ⟨i₀⟩
  exact Finset.le_sup' (f := fun j => power a q j p) (Finset.mem_univ i)

theorem power_continuous {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (i : Fin m) : Continuous (fun p : Fin D → ℝ => power a q i p) := by
  unfold power
  fun_prop

theorem powerMin_continuous {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (i₀ : Fin m) : Continuous (powerMin a q i₀) := by
  unfold powerMin
  letI : Nonempty (Fin m) := ⟨i₀⟩
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    fun i _ => power_continuous a q i

theorem powerMax_continuous {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (i₀ : Fin m) : Continuous (powerMax a q i₀) := by
  unfold powerMax
  letI : Nonempty (Fin m) := ⟨i₀⟩
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    fun i _ => power_continuous a q i

theorem no_equal_powers_of_avoiding {D m : ℕ} (a : Fin m → Fin D → ℝ)
    (q : Fin m → ℝ) (hq : ∀ e : Fin (D + 2) ↪ Fin m, q ∉ badSubspace a e)
    (p : Fin D → ℝ) (e : Fin (D + 2) ↪ Fin m) :
    ¬ ∀ k, power a q (e k) p = power a q (e 0) p := by
  intro hall
  let z := power a q (e 0) p
  let b : Fin (D + 1) → ℝ := Fin.snoc (fun j : Fin D => 2 * p j) z
  have hmem : q ∈ badSubspace a e := by
    change restrict e q ∈ (affineEval a e).range
    refine ⟨b, ?_⟩
    funext k
    change b (Fin.last D) + ∑ j, b (Fin.castSucc j) * a (e k) j = q (e k)
    simp only [b, Fin.snoc_last, Fin.snoc_castSucc]
    have hk : q (e k) - 2 * ∑ j, p j * a (e k) j = z := by
      simpa [z, power] using hall k
    calc
      z + ∑ j, (2 * p j) * a (e k) j = z + 2 * ∑ j, p j * a (e k) j := by
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = q (e k) := by linarith
  exact hq e hmem

def tupleMin {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (e : Fin (D + 2) ↪ Fin m) (p : Fin D → ℝ) : ℝ :=
  letI : Nonempty (Fin (D + 2)) := ⟨0⟩
  Finset.univ.inf' Finset.univ_nonempty (fun k => power a q (e k) p)

def tupleMax {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (e : Fin (D + 2) ↪ Fin m) (p : Fin D → ℝ) : ℝ :=
  letI : Nonempty (Fin (D + 2)) := ⟨0⟩
  Finset.univ.sup' Finset.univ_nonempty (fun k => power a q (e k) p)

def tupleGap {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (e : Fin (D + 2) ↪ Fin m) (p : Fin D → ℝ) : ℝ :=
  tupleMax a q e p - tupleMin a q e p

theorem tupleMin_le {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (e : Fin (D + 2) ↪ Fin m) (p : Fin D → ℝ) (k : Fin (D + 2)) :
    tupleMin a q e p ≤ power a q (e k) p := by
  unfold tupleMin
  letI : Nonempty (Fin (D + 2)) := ⟨0⟩
  exact Finset.inf'_le (f := fun j => power a q (e j) p) (Finset.mem_univ k)

theorem power_le_tupleMax {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (e : Fin (D + 2) ↪ Fin m) (p : Fin D → ℝ) (k : Fin (D + 2)) :
    power a q (e k) p ≤ tupleMax a q e p := by
  unfold tupleMax
  letI : Nonempty (Fin (D + 2)) := ⟨0⟩
  exact Finset.le_sup' (f := fun j => power a q (e j) p) (Finset.mem_univ k)

theorem tupleGap_continuous {D m : ℕ} (a : Fin m → Fin D → ℝ)
    (q : Fin m → ℝ) (e : Fin (D + 2) ↪ Fin m) : Continuous (tupleGap a q e) := by
  unfold tupleGap tupleMin tupleMax
  letI : Nonempty (Fin (D + 2)) := ⟨0⟩
  exact (Continuous.finset_sup'_apply Finset.univ_nonempty
    fun k _ => (power_continuous a q (e k))).sub
    (Continuous.finset_inf'_apply Finset.univ_nonempty
      fun k _ => (power_continuous a q (e k)))

theorem tupleGap_pos_of_avoiding {D m : ℕ} (a : Fin m → Fin D → ℝ)
    (q : Fin m → ℝ) (hq : ∀ e : Fin (D + 2) ↪ Fin m, q ∉ badSubspace a e)
    (p : Fin D → ℝ) (e : Fin (D + 2) ↪ Fin m) : 0 < tupleGap a q e p := by
  have hmin : tupleMin a q e p ≤ tupleMax a q e p :=
    (tupleMin_le a q e p 0).trans (power_le_tupleMax a q e p 0)
  have hlt : tupleMin a q e p < tupleMax a q e p := by
    by_contra h
    have heq : tupleMax a q e p = tupleMin a q e p := le_antisymm (le_of_not_gt h) hmin
    have hall : ∀ k, power a q (e k) p = power a q (e 0) p := by
      intro k
      have hleft := tupleMin_le a q e p k
      have hright := power_le_tupleMax a q e p k
      have heq0 : power a q (e 0) p = tupleMin a q e p :=
        le_antisymm ((power_le_tupleMax a q e p 0).trans heq.le) (tupleMin_le a q e p 0)
      exact (le_antisymm (hright.trans heq.le) hleft).trans heq0.symm
    exact no_equal_powers_of_avoiding a q hq p e hall
  exact sub_pos.mpr hlt

theorem powerMin_le_tupleMin {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (i₀ : Fin m) (e : Fin (D + 2) ↪ Fin m) (p : Fin D → ℝ) :
    powerMin a q i₀ p ≤ tupleMin a q e p := by
  unfold tupleMin
  letI : Nonempty (Fin (D + 2)) := ⟨0⟩
  rw [Finset.le_inf'_iff]
  intro k hk
  exact powerMin_le a q i₀ p (e k)

theorem tupleMax_lt_of_forall_lt {D m : ℕ} (a : Fin m → Fin D → ℝ)
    (q : Fin m → ℝ) (e : Fin (D + 2) ↪ Fin m) (p : Fin D → ℝ) (b : ℝ)
    (h : ∀ k, power a q (e k) p < b) : tupleMax a q e p < b := by
  unfold tupleMax
  letI : Nonempty (Fin (D + 2)) := ⟨0⟩
  rw [Finset.sup'_lt_iff]
  exact fun k _ => h k

noncomputable def meshGap {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (e₀ : Fin (D + 2) ↪ Fin m) (p : Fin D → ℝ) : ℝ :=
  letI : Nonempty (Fin (D + 2) ↪ Fin m) := ⟨e₀⟩
  Finset.univ.inf' Finset.univ_nonempty (fun e => tupleGap a q e p)

theorem meshGap_continuous {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (e₀ : Fin (D + 2) ↪ Fin m) : Continuous (meshGap a q e₀) := by
  unfold meshGap
  letI : Nonempty (Fin (D + 2) ↪ Fin m) := ⟨e₀⟩
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    fun e _ => tupleGap_continuous a q e

theorem meshGap_pos_of_avoiding {D m : ℕ} (a : Fin m → Fin D → ℝ)
    (q : Fin m → ℝ) (hq : ∀ e : Fin (D + 2) ↪ Fin m, q ∉ badSubspace a e)
    (e₀ : Fin (D + 2) ↪ Fin m) (p : Fin D → ℝ) : 0 < meshGap a q e₀ p := by
  letI : Nonempty (Fin (D + 2) ↪ Fin m) := ⟨e₀⟩
  obtain ⟨e, he, hEq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun e => tupleGap a q e p)
  rw [meshGap, hEq]
  exact tupleGap_pos_of_avoiding a q hq p e

theorem meshGap_le {D m : ℕ} (a : Fin m → Fin D → ℝ) (q : Fin m → ℝ)
    (e₀ e : Fin (D + 2) ↪ Fin m) (p : Fin D → ℝ) :
    meshGap a q e₀ p ≤ tupleGap a q e p := by
  unfold meshGap
  letI : Nonempty (Fin (D + 2) ↪ Fin m) := ⟨e₀⟩
  exact Finset.inf'_le (f := fun e' => tupleGap a q e' p) (Finset.mem_univ e)

theorem exists_embedding_into_finset {m n : ℕ} (s : Finset (Fin m))
    (h : n ≤ s.card) : ∃ e : Fin n ↪ Fin m, ∀ i, e i ∈ s := by
  classical
  letI : Fintype {i : Fin m // i ∈ s} := Fintype.ofFinite _
  have hcard : n ≤ Fintype.card {i : Fin m // i ∈ s} := by simpa using h
  let f : Fin n ↪ {i : Fin m // i ∈ s} :=
    (Fin.castLEEmb hcard).trans (Fintype.equivFin {i : Fin m // i ∈ s}).symm.toEmbedding
  let e : Fin n ↪ Fin m := f.trans (Function.Embedding.subtype (fun i : Fin m => i ∈ s))
  refine ⟨e, ?_⟩
  intro i
  exact (f i).property

end HypercubeRamsey.Lane_q_mesh
