import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.StdSimplex

namespace HypercubeRamsey.Lane_q_s10_d4

open scoped BigOperators

/-- A finite price response gives a mixture whose coordinates are bounded by
the target vector. -/
theorem finite_mixture_le_of_price_bound {A K : Type*} [Fintype A] [Fintype K]
    (v : A → K → ℝ) (b : K → ℝ)
    (hprice : ∀ c : K → ℝ, (∀ k, 0 ≤ c k) →
      ∃ a : A, ∑ k, c k * v a k ≤ ∑ k, c k * b k) :
    ∃ w : A → ℝ, (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 ∧
      ∀ k, ∑ a, w a * v a k ≤ b k := by
  classical
  by_contra hNo
  let V := K → ℝ
  let L : (A → ℝ) →ₗ[ℝ] V := {
    toFun := fun w k => ∑ a, w a * v a k
    map_add' := by
      intro w₁ w₂
      ext k
      change (∑ a, (w₁ a + w₂ a) * v a k) =
        (∑ a, w₁ a * v a k) + ∑ a, w₂ a * v a k
      calc
        (∑ a, (w₁ a + w₂ a) * v a k) =
            ∑ a, (w₁ a * v a k + w₂ a * v a k) := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = (∑ a, w₁ a * v a k) + ∑ a, w₂ a * v a k := by
          rw [Finset.sum_add_distrib]
    map_smul' := by
      intro r w
      ext k
      change (∑ a, (r * w a) * v a k) = r * (∑ a, w a * v a k)
      calc
        (∑ a, (r * w a) * v a k) = ∑ a, r * (w a * v a k) := by
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = r * ∑ a, w a * v a k := by rw [Finset.mul_sum]
  }
  let C : Set V := L '' stdSimplex ℝ A
  let D : Set V := {z | ∀ k, z k ≤ b k}
  have hCconv : Convex ℝ C := (convex_stdSimplex ℝ A).linear_image L
  have hCcompact : IsCompact C :=
    (isCompact_stdSimplex ℝ A).image L.continuous_of_finiteDimensional
  have hDconv : Convex ℝ D := by
    intro x hx y hy r s hr hs hrs k
    change r * x k + s * y k ≤ b k
    calc
      r * x k + s * y k ≤ r * b k + s * b k := by
        exact add_le_add (mul_le_mul_of_nonneg_left (hx k) hr)
          (mul_le_mul_of_nonneg_left (hy k) hs)
      _ = b k := by rw [← add_mul, hrs, one_mul]
  have hDclosed : IsClosed D := by
    rw [show D = ⋂ k : K, {z : V | z k ≤ b k} by ext z; simp [D]]
    exact isClosed_iInter fun k => isClosed_le (continuous_apply k) continuous_const
  have hno : ¬ ∃ w : A → ℝ, (∀ a, 0 ≤ w a) ∧ ∑ a, w a = 1 ∧
      ∀ k, ∑ a, w a * v a k ≤ b k := by
    rintro ⟨w, hw0, hw1, hw⟩
    apply hNo
    refine ⟨w, hw0, hw1, ?_⟩
    intro k
    exact hw k
  have hdisj : Disjoint C D := by
    apply Set.disjoint_left.mpr
    intro z hzC hzD
    rcases hzC with ⟨w, hw, rfl⟩
    apply hno
    refine ⟨w, hw.1, hw.2, ?_⟩
    intro k
    exact hzD k
  obtain ⟨f, u, v₀, hfC, huv, hfD⟩ :=
    geometric_hahn_banach_compact_closed hCconv hCcompact hDconv hDclosed hdisj
  let lam : K → ℝ := fun k => f (Pi.single (M := fun _ : K => ℝ) k (1 : ℝ))
  have frepr (z : V) : f z = ∑ k, z k * lam k := by
    have hdecomp : z = ∑ k, z k • Pi.single k (1 : ℝ) := by
      exact pi_eq_sum_univ' z
    calc
      f z = f (∑ k, z k • (Pi.single k (1 : ℝ))) := by rw [← hdecomp]
      _ = ∑ k, z k * lam k := by
        simp [lam, smul_eq_mul]
  have hlamnonpos (k : K) : lam k ≤ 0 := by
    by_contra hnot
    have hlampos : 0 < lam k := lt_of_not_ge hnot
    let q : ℝ := (f b - v₀) / lam k
    obtain ⟨m, hm⟩ := exists_nat_gt q
    let z : V := b - (m : ℝ) • Pi.single (M := fun _ : K => ℝ) k (1 : ℝ)
    have hzD : z ∈ D := by
      intro j
      by_cases hkj : k = j
      · subst j
        simp [z, Pi.single_eq_same]
      · have hjk : j ≠ k := Ne.symm hkj
        simp [z, Pi.single_eq_of_ne hjk]
    have hfz : f z = f b - (m : ℝ) * lam k := by
      change f (b - (m : ℝ) • Pi.single (M := fun _ : K => ℝ) k 1) = _
      rw [map_sub, map_smul]
      simp [lam, smul_eq_mul]
    have hmul : f b - v₀ < (m : ℝ) * lam k := by
      have h := (div_lt_iff₀ hlampos).mp hm
      simpa [q] using h
    have hvz := hfD z hzD
    rw [hfz] at hvz
    linarith
  let price : K → ℝ := fun k => -lam k
  have hprice' : ∀ k, 0 ≤ price k := by
    intro k
    exact neg_nonneg.mpr (hlamnonpos k)
  obtain ⟨a, ha⟩ := hprice price hprice'
  have haC : L (Pi.single a (1 : ℝ)) ∈ C := by
    exact ⟨Pi.single a (1 : ℝ), single_mem_stdSimplex ℝ a, rfl⟩
  have hfLa : f (L (Pi.single a (1 : ℝ))) < u := hfC _ haC
  have hLsingle : L (Pi.single a (1 : ℝ)) = v a := by
    funext k
    simp [L, Pi.single_apply]
  have hfLa' : f (L (Pi.single a (1 : ℝ))) =
      -∑ k, price k * v a k := by
    rw [frepr, hLsingle]
    simp [price, mul_comm]
  have hfB : v₀ < f b := hfD b (by intro k; exact le_rfl)
  have hfB' : f b = -∑ k, price k * b k := by
    rw [frepr]
    simp [price, mul_comm]
  have hstrict : f (L (Pi.single a (1 : ℝ))) < f b :=
    lt_trans hfLa (lt_trans huv hfB)
  rw [hfLa', hfB'] at hstrict
  linarith

end HypercubeRamsey.Lane_q_s10_d4
