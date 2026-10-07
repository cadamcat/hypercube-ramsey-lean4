import Mathlib
import HypercubeRamsey.Tools.Mesh_q_mesh

/-!
# Finite-dimensional Kuhn mesh

F-Mesh returns a locally supported continuous partition of unity on a compact convex parameter set. The
active-vertex bound `D+1` is essential to the finite history-count estimates in Part C.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- F-Mesh (X-Kuhn): for any nonempty compact convex `K ⊆ ℝ^D` and `r > 0`, there is a finite family of
continuous partition-of-unity weights whose positive support has at most `D+1` vertices, each based in `K`
within coordinate distance `r` of the parameter. -/
theorem exists_finite_mesh (D : ℕ) (K : Set (Fin D → ℝ)) (hKne : K.Nonempty)
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K) (r : ℝ) (hr : 0 < r) :
    ∃ m : ℕ,
      ∃ base : Fin m → {p : Fin D → ℝ // p ∈ K},
      ∃ weight : Fin m → {p : Fin D → ℝ // p ∈ K} → ℝ,
        (∀ v, Continuous (weight v)) ∧
        (∀ v p, 0 ≤ weight v p) ∧
        (∀ p, ∑ v, weight v p = 1) ∧
        (∀ v p, 0 < weight v p → ∀ j : Fin D,
          |p.1 j - (base v).1 j| ≤ r) ∧
        (∀ p, (Finset.univ.filter (fun v => 0 < weight v p)).card ≤ D + 1) := by
  classical
  let η : ℝ := r / (4 * ((D : ℝ) + 1))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨t, htK, htFin, hcover⟩ := hKcompact.finite_cover_balls hη
  let s : Finset (Fin D → ℝ) := htFin.toFinset
  letI : Fintype (↥s) := Fintype.ofFinite _
  let n : ℕ := Fintype.card (↥s)
  let m : ℕ := n + (D + 2)
  obtain ⟨x₀, hx₀⟩ := hKne
  let eS : (↥s) ≃ Fin n := Fintype.equivFin _
  let first : Fin n → {x : Fin D → ℝ // x ∈ K} := fun i =>
    ⟨(eS.symm i).val, htK (htFin.mem_toFinset.mp (by simpa [s] using (eS.symm i).property))⟩
  let base : Fin m → {x : Fin D → ℝ // x ∈ K} :=
    Fin.append first (fun _ => ⟨x₀, hx₀⟩)
  let a : Fin m → Fin D → ℝ := fun i => (base i).val
  let e₀ : Fin (D + 2) ↪ Fin m := Fin.natAddEmb n
  let i₀ : Fin m := e₀ 0
  have hnet : ∀ p ∈ K, ∃ k : Fin n,
      dist p (a (Fin.castAdd (D + 2) k)) < η := by
    intro p hp
    rcases Set.mem_iUnion.mp (hcover hp) with ⟨x, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hxt, hball⟩
    have hxS : x ∈ s := by
      apply (htFin.mem_toFinset).mpr
      simpa [s] using hxt
    let y : ↥s := ⟨x, hxS⟩
    refine ⟨eS y, ?_⟩
    have hbase : a (Fin.castAdd (D + 2) (eS y)) = x := by
      simp [a, base, first, Fin.append_left]
      rfl
    rw [hbase]
    exact hball
  let q₀ : Fin m → ℝ := fun i => HypercubeRamsey.Lane_q_mesh.sqNorm (a i)
  let ε : ℝ := r ^ 2 / 16
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨q, hqgeneric, hqclose⟩ :=
    HypercubeRamsey.Lane_q_mesh.exists_small_avoiding_badSubspaces a q₀ hε
  have hgapPos : ∀ p ∈ K, 0 < HypercubeRamsey.Lane_q_mesh.meshGap a q e₀ p := by
    intro p hp
    exact HypercubeRamsey.Lane_q_mesh.meshGap_pos_of_avoiding a q hqgeneric e₀ p
  obtain ⟨γ, hγpos, hγ⟩ := hKcompact.exists_forall_le'
    (HypercubeRamsey.Lane_q_mesh.meshGap_continuous a q e₀).continuousOn
    (a := 0) hgapPos
  let δ : ℝ := min (γ / 2) (r ^ 2 / 4)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by positivity)
  have hδgap : δ < γ := by
    dsimp [δ]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδsmall : δ ≤ r ^ 2 / 4 := by
    dsimp [δ]
    exact min_le_right _ _
  let μ : (Fin D → ℝ) → ℝ := HypercubeRamsey.Lane_q_mesh.powerMin a q i₀
  let raw : Fin m → (Fin D → ℝ) → ℝ := fun i p =>
    max 0 (δ + μ p - HypercubeRamsey.Lane_q_mesh.power a q i p)
  let den : (Fin D → ℝ) → ℝ := fun p => ∑ i, raw i p
  let weight : Fin m → {p : Fin D → ℝ // p ∈ K} → ℝ := fun i p => raw i p.1 / den p.1
  have hrawnonneg : ∀ i p, 0 ≤ raw i p := by
    intro i p
    simp [raw]
  have hdenpos : ∀ p : Fin D → ℝ, 0 < den p := by
    intro p
    letI : Nonempty (Fin m) := ⟨i₀⟩
    obtain ⟨i, hi, hmin⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun j => HypercubeRamsey.Lane_q_mesh.power a q j p)
    have hμ : μ p = HypercubeRamsey.Lane_q_mesh.power a q i p := by
      simpa [μ, HypercubeRamsey.Lane_q_mesh.powerMin] using hmin
    have hraw : raw i p = δ := by
      simp [raw, hμ, hδpos.le]
    have hsum : raw i p ≤ den p := by
      dsimp [den]
      exact Finset.single_le_sum (f := fun j : Fin m => raw j p)
        (fun j _ => hrawnonneg j p) (Finset.mem_univ i)
    rw [hraw] at hsum
    exact lt_of_lt_of_le hδpos hsum
  have hrawcont : ∀ i, Continuous (fun p : Fin D → ℝ => raw i p) := by
    intro i
    dsimp [raw, μ]
    exact continuous_const.max
      ((continuous_const.add (HypercubeRamsey.Lane_q_mesh.powerMin_continuous a q i₀)).sub
        (HypercubeRamsey.Lane_q_mesh.power_continuous a q i))
  have hdencont : Continuous den := by
    dsimp [den]
    exact continuous_finsetSum Finset.univ (fun i _ => hrawcont i)
  have hweightcont : ∀ i, Continuous (weight i) := by
    intro i
    dsimp [weight]
    exact Continuous.div
      ((hrawcont i).comp continuous_subtype_val)
      (hdencont.comp continuous_subtype_val)
      (fun p => ne_of_gt (hdenpos p.1))
  have hweightnonneg : ∀ i p, 0 ≤ weight i p := by
    intro i p
    dsimp [weight]
    exact div_nonneg (hrawnonneg i p.1) (le_of_lt (hdenpos p.1))
  have hweightsum : ∀ p, ∑ i, weight i p = 1 := by
    intro p
    dsimp [weight]
    calc
      (∑ i : Fin m, raw i p.1 / den p.1) =
          (∑ i ∈ Finset.univ, raw i p.1) / den p.1 := by
        symm
        simpa using Finset.sum_div Finset.univ (fun i => raw i p.1) (den p.1)
      _ = 1 := by
        simp [den, ne_of_gt (hdenpos p.1)]
  have hweightpos_bound : ∀ i (p : {x : Fin D → ℝ // x ∈ K}),
      0 < weight i p →
      HypercubeRamsey.Lane_q_mesh.power a q i p.1 < δ + μ p.1 := by
    intro i p hwi
    have hrawpos : 0 < raw i p.1 :=
      (div_pos_iff_of_pos_right (hdenpos p.1)).mp (by simpa [weight] using hwi)
    have hx : 0 < δ + μ p.1 - HypercubeRamsey.Lane_q_mesh.power a q i p.1 := by
      simpa [raw] using hrawpos
    linarith
  have hsupport : ∀ p : {x : Fin D → ℝ // x ∈ K},
      (Finset.univ.filter (fun i => 0 < weight i p)).card ≤ D + 1 := by
    intro p
    let active := Finset.univ.filter (fun i : Fin m => 0 < weight i p)
    by_contra hcard
    have hlarge : D + 2 ≤ active.card := by
      dsimp [active]
      omega
    obtain ⟨e, heactive⟩ := HypercubeRamsey.Lane_q_mesh.exists_embedding_into_finset active hlarge
    have hupper : ∀ k, HypercubeRamsey.Lane_q_mesh.power a q (e k) p.1 < δ + μ p.1 := by
      intro k
      exact hweightpos_bound (e k) p ((Finset.mem_filter.mp (heactive k)).2)
    have hmax : HypercubeRamsey.Lane_q_mesh.tupleMax a q e p.1 < δ + μ p.1 :=
      HypercubeRamsey.Lane_q_mesh.tupleMax_lt_of_forall_lt a q e p.1 (δ + μ p.1) hupper
    have hmin : μ p.1 ≤ HypercubeRamsey.Lane_q_mesh.tupleMin a q e p.1 := by
      exact HypercubeRamsey.Lane_q_mesh.powerMin_le_tupleMin a q i₀ e p.1
    have htuple : HypercubeRamsey.Lane_q_mesh.tupleGap a q e p.1 < δ := by
      dsimp [HypercubeRamsey.Lane_q_mesh.tupleGap]
      linarith
    have hmesh : γ ≤ HypercubeRamsey.Lane_q_mesh.tupleGap a q e p.1 :=
      (hγ p.1 p.2).trans (HypercubeRamsey.Lane_q_mesh.meshGap_le a q e₀ e p.1)
    linarith
  have hηbound : (D : ℝ) * η ^ 2 ≤ r ^ 2 / 16 := by
    have hD : (D : ℝ) ≤ ((D : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (D : ℝ)]
    have hdenη : 0 < 16 * ((D : ℝ) + 1) ^ 2 := by positivity
    have hratio : (D : ℝ) / (16 * ((D : ℝ) + 1) ^ 2) ≤ (1 : ℝ) / 16 := by
      rw [div_le_iff₀ hdenη]
      nlinarith [hD]
    have hηden : 4 * ((D : ℝ) + 1) ≠ 0 := by positivity
    calc
      (D : ℝ) * η ^ 2 = r ^ 2 * ((D : ℝ) / (16 * ((D : ℝ) + 1) ^ 2)) := by
        dsimp [η]
        field_simp [hηden]
        ring
      _ ≤ r ^ 2 * ((1 : ℝ) / 16) := mul_le_mul_of_nonneg_left hratio (sq_nonneg r)
      _ = r ^ 2 / 16 := by ring
  refine ⟨m, base, weight, ?_, ?_, ?_, ?_, hsupport⟩
  · exact hweightcont
  · exact hweightnonneg
  · exact hweightsum
  · intro i p hwi j
    obtain ⟨k, hk⟩ := hnet p.1 p.2
    let k' : Fin m := Fin.castAdd (D + 2) k
    have hpower : HypercubeRamsey.Lane_q_mesh.power a q i p.1 <
        HypercubeRamsey.Lane_q_mesh.power a q k' p.1 + δ := by
      have hmin := HypercubeRamsey.Lane_q_mesh.powerMin_le a q i₀ p.1 k'
      have hi := hweightpos_bound i p hwi
      dsimp [μ] at hi
      linarith
    have hid : HypercubeRamsey.Lane_q_mesh.power a q i p.1 +
        HypercubeRamsey.Lane_q_mesh.sqNorm p.1 =
        HypercubeRamsey.Lane_q_mesh.sqDist p.1 (a i) + (q i - q₀ i) := by
      simpa [q₀] using HypercubeRamsey.Lane_q_mesh.power_sqDist_identity a q i p.1
    have hkd : HypercubeRamsey.Lane_q_mesh.power a q k' p.1 +
        HypercubeRamsey.Lane_q_mesh.sqNorm p.1 =
        HypercubeRamsey.Lane_q_mesh.sqDist p.1 (a k') + (q k' - q₀ k') := by
      simpa [q₀] using HypercubeRamsey.Lane_q_mesh.power_sqDist_identity a q k' p.1
    have hsqcomp : HypercubeRamsey.Lane_q_mesh.sqDist p.1 (a i) + (q i - q₀ i) <
        HypercubeRamsey.Lane_q_mesh.sqDist p.1 (a k') + (q k' - q₀ k') + δ := by
      nlinarith [hpower, hid, hkd]
    have hpertI : -ε < q i - q₀ i := (abs_lt.mp (hqclose i)).1
    have hpertK : q k' - q₀ k' < ε := (abs_lt.mp (hqclose k')).2
    have hsq : HypercubeRamsey.Lane_q_mesh.sqDist p.1 (a i) <
        (D : ℝ) * η ^ 2 + δ + 2 * ε := by
      have hreference : HypercubeRamsey.Lane_q_mesh.sqDist p.1 (a k') ≤ (D : ℝ) * η ^ 2 := by
        have hcoord : ∀ l : Fin D, |p.1 l - a k' l| ≤ η := by
          intro l
          have hpi : dist (p.1 l) (a k' l) ≤ dist p.1 (a k') :=
            (dist_pi_le_iff (dist_nonneg : (0 : ℝ) ≤ dist p.1 (a k'))).mp
              (le_rfl : dist p.1 (a k') ≤ dist p.1 (a k')) l
          simpa [Real.dist_eq] using hpi.trans (le_of_lt hk)
        simpa [HypercubeRamsey.Lane_q_mesh.sqDist] using
          (HypercubeRamsey.Lane_q_mesh.sum_sq_le_of_abs_le
            (fun l => p.1 l - a k' l) η hη.le hcoord)
      linarith
    have hcoordSq : (p.1 j - a i j) ^ 2 < r ^ 2 := by
      have hterm : (p.1 j - a i j) ^ 2 ≤
          HypercubeRamsey.Lane_q_mesh.sqDist p.1 (a i) := by
        unfold HypercubeRamsey.Lane_q_mesh.sqDist
        exact Finset.single_le_sum (f := fun l : Fin D => (p.1 l - a i l) ^ 2)
          (fun l _ => sq_nonneg _) (Finset.mem_univ j)
      dsimp [ε] at hsq
      nlinarith [hterm, hηbound, hδsmall]
    have habs : |p.1 j - a i j| ≤ r := by
      apply (sq_le_sq₀ (abs_nonneg _) hr.le).1
      simpa only [sq_abs] using le_of_lt hcoordSq
    exact habs

end HypercubeRamsey
