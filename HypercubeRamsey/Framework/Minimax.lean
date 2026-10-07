import HypercubeRamsey.Framework.FinProb
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Finite minimax and separation

The price-separation arguments of the paper (Lemma 3.3 and its uses in Sections 4–5 and later) in two forms.
-/

namespace HypercubeRamsey

/-- Finite minimax: if every mixed column strategy is answered by a row with nonpositive payoff, some mixed
row strategy has nonpositive payoff against every column. -/
theorem finite_minimax {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (M : A → B → ℝ) (h : ∀ q : FinProb B, ∃ a, ∑ b, q.w b * M a b ≤ 0) :
    ∃ p : FinProb A, ∀ b, ∑ a, p.w a * M a b ≤ 0 := by
  classical
  by_contra hNo
  let V := B → ℝ
  let L : (A → ℝ) →ₗ[ℝ] V := {
    toFun := fun q b => ∑ a, q a * M a b
    map_add' := by
      intro q r
      ext b
      change (∑ a, (q a + r a) * M a b) =
        (∑ a, q a * M a b) + ∑ a, r a * M a b
      calc
        (∑ a, (q a + r a) * M a b) = ∑ a, (q a * M a b + r a * M a b) := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = (∑ a, q a * M a b) + ∑ a, r a * M a b := by rw [Finset.sum_add_distrib]
    map_smul' := by
      intro c q
      ext b
      change (∑ a, c * q a * M a b) = c * ∑ a, q a * M a b
      calc
        (∑ a, c * q a * M a b) = ∑ a, c * (q a * M a b) := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = c * ∑ a, q a * M a b := by rw [Finset.mul_sum]
  }
  let C : Set V := L '' stdSimplex ℝ A
  let D : Set V := {x | ∀ b, x b ≤ 0}
  have hCconv : Convex ℝ C := (convex_stdSimplex ℝ A).linear_image L
  have hCcompact : IsCompact C :=
    (isCompact_stdSimplex ℝ A).image L.continuous_of_finiteDimensional
  have hDconv : Convex ℝ D := by
    intro x hx y hy α β hα hβ hαβ b
    change α * x b + β * y b ≤ 0
    nlinarith [hx b, hy b]
  have hDclosed : IsClosed D := by
    rw [show D = ⋂ b : B, {x : V | x b ≤ 0} by ext x; simp [D]]
    exact isClosed_iInter fun b => isClosed_le (continuous_apply b) continuous_const
  have hdisj : Disjoint C D := by
    apply Set.disjoint_left.mpr
    intro x hxC hxD
    rcases hxC with ⟨q, hq, rfl⟩
    apply hNo
    refine ⟨⟨q, hq.1, hq.2⟩, ?_⟩
    intro b
    simpa [L] using hxD b
  obtain ⟨f, u, v, hfC, huv, hfD⟩ :=
    geometric_hahn_banach_compact_closed hCconv hCcompact hDconv hDclosed hdisj
  let basis : B → V := fun b j => if b = j then 1 else 0
  let lam : B → ℝ := fun b => f (basis b)
  have frepr (x : V) : f x = ∑ b, x b * lam b := by
    calc
      f x = f (∑ b, x b • basis b) := by congr 1; exact pi_eq_sum_univ x
      _ = ∑ b, x b * lam b := by simp [lam, basis, smul_eq_mul]
  have hlam : ∀ b, lam b ≤ 0 := by
    intro b
    by_contra hnot
    have hlam_pos : 0 < lam b := lt_of_not_ge hnot
    let q : ℝ := -v / lam b
    obtain ⟨n, hn⟩ := exists_nat_gt q
    let x : V := -((n : ℝ) • basis b)
    have hxD : x ∈ D := by
      intro j
      change -((n : ℝ) * basis b j) ≤ 0
      by_cases hj : b = j
      · subst j
        simp [basis]
      · simp [basis, hj]
    have hfx : f x = -(n : ℝ) * lam b := by
      change f (-((n : ℝ) • basis b)) = -(n : ℝ) * lam b
      rw [map_neg, map_smul]
      simp [lam, smul_eq_mul]
    have hlarge : -v < (n : ℝ) * lam b := by
      have h := (div_lt_iff₀ hlam_pos).mp hn
      simpa [q] using h
    have h := hfD x hxD
    rw [hfx] at h
    linarith
  let c : B → ℝ := fun b => -lam b
  have hc (b : B) : 0 ≤ c b := neg_nonneg.mpr (hlam b)
  have hvzero : v < 0 := by
    have h := hfD (0 : V) (by intro b; exact le_rfl)
    simpa using h
  have huzero : u < 0 := huv.trans hvzero
  have hrow_mem (a : A) : (fun b => M a b) ∈ C := by
    refine ⟨Pi.single a 1, single_mem_stdSimplex ℝ a, ?_⟩
    funext b
    simp [L, Pi.single_apply]
  have hrow (a : A) : 0 < ∑ b, c b * M a b := by
    have hfrow : f (fun b => M a b) < 0 := (hfC _ (hrow_mem a)).trans huzero
    have hrepr : ∑ b, c b * M a b = -f (fun b => M a b) := by
      calc
        ∑ b, c b * M a b = ∑ b, -((fun j => M a j) b * lam b) := by
          apply Finset.sum_congr rfl
          intro b hb
          simp [c]
          ring
        _ = -(∑ b, (fun j => M a j) b * lam b) := by rw [Finset.sum_neg_distrib]
        _ = -f (fun b => M a b) := by rw [frepr]
    rw [hrepr]
    linarith
  let P : ℝ := ∑ b, c b
  have hP_nonneg : 0 ≤ P := by
    apply Finset.sum_nonneg
    intro b hb
    exact hc b
  have hP_pos : 0 < P := by
    by_contra hnot
    have hPzero : P = 0 := le_antisymm (le_of_not_gt hnot) hP_nonneg
    obtain ⟨a⟩ := ‹Nonempty A›
    have hc_zero (b : B) : c b = 0 := by
      have hle : c b ≤ P := by
        dsimp [P]
        exact Finset.single_le_sum (fun j hj => hc j) (Finset.mem_univ b)
      linarith [hc b]
    have hrow_zero : ∑ b, c b * M a b = 0 := by simp [hc_zero]
    have hrow_pos_a := hrow a
    rw [hrow_zero] at hrow_pos_a
    norm_num at hrow_pos_a
  let q : FinProb B := {
    w := fun b => c b / P
    nonneg := fun b => div_nonneg (hc b) hP_nonneg
    sum_eq_one := by
      rw [← Finset.sum_div]
      change P / P = 1
      exact div_self (ne_of_gt hP_pos)
  }
  obtain ⟨a, ha⟩ := h q
  have hqval : 0 < ∑ b, q.w b * M a b := by
    calc
      ∑ b, q.w b * M a b = ∑ b, (c b * M a b) / P := by
        apply Finset.sum_congr rfl
        intro b hb
        dsimp [q]
        field_simp [ne_of_gt hP_pos]
        <;> ring
      _ = (∑ b, c b * M a b) / P := by rw [Finset.sum_div]
      _ > 0 := div_pos (hrow a) hP_pos
  linarith

/-- Separation in coordinates: a point outside the convex hull of finitely many vectors is strictly separated
by a linear functional. -/
theorem exists_separating_of_not_mem_convexHull {ι K : Type*} [Fintype ι] [Fintype K]
    (v : ι → K → ℝ) (p : K → ℝ)
    (h : ¬ ∃ ρ : FinProb ι, ∀ k, ∑ i, ρ.w i * v i k = p k) :
    ∃ c : K → ℝ, ∀ i, ∑ k, c k * v i k < ∑ k, c k * p k := by
  classical
  by_cases hι : Nonempty ι
  · let V := K → ℝ
    let L : (ι → ℝ) →ₗ[ℝ] V := {
      toFun := fun ρ k => ∑ i, ρ i * v i k
      map_add' := by
        intro ρ σ
        ext k
        change (∑ i, (ρ i + σ i) * v i k) =
          (∑ i, ρ i * v i k) + ∑ i, σ i * v i k
        calc
          (∑ i, (ρ i + σ i) * v i k) = ∑ i, (ρ i * v i k + σ i * v i k) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = (∑ i, ρ i * v i k) + ∑ i, σ i * v i k := by rw [Finset.sum_add_distrib]
      map_smul' := by
        intro a ρ
        ext k
        change (∑ i, a * ρ i * v i k) = a * ∑ i, ρ i * v i k
        calc
          (∑ i, a * ρ i * v i k) = ∑ i, a * (ρ i * v i k) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = a * ∑ i, ρ i * v i k := by rw [Finset.mul_sum]
    }
    let C : Set V := L '' stdSimplex ℝ ι
    have hCconv : Convex ℝ C := (convex_stdSimplex ℝ ι).linear_image L
    have hCcompact : IsCompact C :=
      (isCompact_stdSimplex ℝ ι).image L.continuous_of_finiteDimensional
    have hpC : p ∉ C := by
      rintro ⟨ρ, hρ, hρp⟩
      apply h
      refine ⟨⟨ρ, hρ.1, hρ.2⟩, ?_⟩
      intro k
      simpa [L] using congrFun hρp k
    have hpclosed : IsClosed C := hCcompact.isClosed
    obtain ⟨f, u, hfp, hfC⟩ := geometric_hahn_banach_point_closed hCconv hpclosed hpC
    let basis : K → V := fun k j => if k = j then 1 else 0
    let lam : K → ℝ := fun k => f (basis k)
    have frepr (x : V) : f x = ∑ k, x k * lam k := by
      calc
        f x = f (∑ k, x k • basis k) := by congr 1; exact pi_eq_sum_univ x
        _ = ∑ k, x k * lam k := by simp [lam, basis, smul_eq_mul]
    let c : K → ℝ := fun k => -lam k
    have hnegfrepr (x : V) : ∑ k, c k * x k = -f x := by
      calc
        ∑ k, c k * x k = ∑ k, - (x k * lam k) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp [c]
          ring
        _ = -(∑ k, x k * lam k) := by rw [Finset.sum_neg_distrib]
        _ = -f x := by rw [frepr]
    refine ⟨c, ?_⟩
    intro i
    have hvi : (v i) ∈ C := by
      refine ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, ?_⟩
      funext k
      simp [L, Pi.single_apply]
    have hstrict : f p < f (v i) := hfp.trans (hfC (v i) hvi)
    have hleft := hnegfrepr (v i)
    have hright := hnegfrepr p
    rw [hleft, hright]
    linarith
  · refine ⟨fun _ => 0, ?_⟩
    intro i
    exact (hι ⟨i⟩).elim

end HypercubeRamsey
