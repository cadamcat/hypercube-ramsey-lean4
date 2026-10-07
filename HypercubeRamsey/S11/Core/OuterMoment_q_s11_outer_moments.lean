import HypercubeRamsey.S11.Core.Definitions

namespace HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer

open Classical
open scoped BigOperators

theorem tuple_expectation_prod {u N : ℕ} (σ : Fin N → ℝ)
    (F : Fin u → Fin N → ℝ) :
    (∑ x : Fin u → Fin N, tupWt σ x * ∏ i, F i (x i)) =
      ∏ i : Fin u, ∑ z, σ z * F i z := by
  classical
  calc
    (∑ x : Fin u → Fin N, tupWt σ x * ∏ i, F i (x i)) =
        ∑ x : Fin u → Fin N, ∏ i : Fin u, σ (x i) * F i (x i) := by
          apply Finset.sum_congr rfl
          intro x hx
          unfold tupWt
          rw [← Finset.prod_mul_distrib]
    _ = ∏ i : Fin u, ∑ z, σ z * F i z := by
          symm
          exact Fintype.prod_sum (fun i z => σ z * F i z)

theorem tuple_interaction_second_moment {u N : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour) (σ π : Fin N → ℝ)
    (hσsum : ∑ x, σ x = 1) (J : Finset (Fin u)) :
    (∑ x : Fin u → Fin N, tupWt σ x * (inter E G π J x) ^ 2) =
      ∑ y, ∑ y', π y * π y' *
        (∑ z, σ z * aF E G π z y * aF E G π z y') ^ J.card := by
  classical
  let H (x : Fin u → Fin N) (y : Fin N) : ℝ :=
    ∏ j ∈ J, aF E G π (x j) y
  let F (y y' : Fin N) (i : Fin u) (z : Fin N) : ℝ :=
    if i ∈ J then aF E G π z y * aF E G π z y' else 1
  have hfilter (f : Fin u → ℝ) :
      (∏ i : Fin u, if i ∈ J then f i else 1) = ∏ i ∈ J, f i := by
    have hJ : Finset.univ.filter (fun i : Fin u => i ∈ J) = J := by
      ext i
      simp
    rw [← Finset.prod_filter (s := Finset.univ) (p := fun i : Fin u => i ∈ J) (f := f)]
    simp [hJ]
  have hHprod (x : Fin u → Fin N) (y y' : Fin N) :
      H x y * H x y' = ∏ i : Fin u, F y y' i (x i) := by
    dsimp [H, F]
    rw [hfilter]
    rw [← Finset.prod_mul_distrib]
  have hFfactor (y y' : Fin N) :
      (∏ i : Fin u, ∑ z, σ z * F y y' i z) =
        (∑ z, σ z * aF E G π z y * aF E G π z y') ^ J.card := by
    let K : ℝ := ∑ z, σ z * aF E G π z y * aF E G π z y'
    calc
      (∏ i : Fin u, ∑ z, σ z * F y y' i z) =
          ∏ i : Fin u, if i ∈ J then K else 1 := by
            apply Finset.prod_congr rfl
            intro i hi
            by_cases hij : i ∈ J
            · simp [F, K, hij]
              ring
            · simp [F, K, hij, hσsum]
      _ = K ^ J.card := by
            rw [hfilter (fun _ => K)]
            simp [Finset.prod_const, K]

  calc
    (∑ x : Fin u → Fin N, tupWt σ x * (inter E G π J x) ^ 2) =
        ∑ x, tupWt σ x *
          ((∑ y, π y * H x y) * (∑ y', π y' * H x y')) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp [inter, H, pow_two]
    _ = ∑ x, tupWt σ x *
          ∑ y, ∑ y', π y * π y' * (H x y * H x y') := by
            apply Finset.sum_congr rfl
            intro x hx
            congr 1
            rw [Finset.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro y hy
            apply Finset.sum_congr rfl
            intro y' hy'
            ring
    _ = ∑ y, ∑ y', π y * π y' *
          (∑ x, tupWt σ x * (H x y * H x y')) := by
            calc
              (∑ x, tupWt σ x *
                  ∑ y, ∑ y', π y * π y' * (H x y * H x y')) =
                  ∑ x, ∑ y, ∑ y',
                    tupWt σ x * (π y * π y' * (H x y * H x y')) := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro y hy
                      rw [Finset.mul_sum]
              _ = ∑ y, ∑ x, ∑ y',
                    tupWt σ x * (π y * π y' * (H x y * H x y')) := by
                      exact Finset.sum_comm
              _ = ∑ y, ∑ y', ∑ x,
                    tupWt σ x * (π y * π y' * (H x y * H x y')) := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      exact Finset.sum_comm
              _ = ∑ y, ∑ y', π y * π y' *
                    (∑ x, tupWt σ x * (H x y * H x y')) := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      apply Finset.sum_congr rfl
                      intro y' hy'
                      calc
                        (∑ x, tupWt σ x * (π y * π y' * (H x y * H x y'))) =
                            ∑ x, (π y * π y') *
                              (tupWt σ x * (H x y * H x y')) := by
                                apply Finset.sum_congr rfl
                                intro x hx
                                ring
                        _ = π y * π y' *
                              (∑ x, tupWt σ x * (H x y * H x y')) := by
                                rw [Finset.mul_sum]
    _ = ∑ y, ∑ y', π y * π y' *
          (∑ z, σ z * aF E G π z y * aF E G π z y') ^ J.card := by
            apply Finset.sum_congr rfl
            intro y hy
            apply Finset.sum_congr rfl
            intro y' hy'
            congr 1
            calc
              (∑ x, tupWt σ x * (H x y * H x y')) =
                  ∑ x, tupWt σ x * ∏ i : Fin u, F y y' i (x i) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    rw [hHprod]
              _ = ∏ i : Fin u, ∑ z, σ z * F y y' i z :=
                    tuple_expectation_prod σ (F y y')
              _ = (∑ z, σ z * aF E G π z y * aF E G π z y') ^ J.card := hFfactor y y'

end HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer
