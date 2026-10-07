import HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer_moments
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer

open Classical
open scoped BigOperators

theorem pi_product_expectation_prod {I : Type*} {N : ℕ} [Fintype I] [DecidableEq I]
    (Q : Law N) (F : I → Fin N → ℝ) :
    (∑ z : I → Fin N, (∏ i, Q.w (z i)) * ∏ i, F i (z i)) =
      ∏ i : I, ∑ x, Q.w x * F i x := by
  classical
  calc
    (∑ z : I → Fin N, (∏ i, Q.w (z i)) * ∏ i, F i (z i)) =
        ∑ z : I → Fin N, ∏ i : I, Q.w (z i) * F i (z i) := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [← Finset.prod_mul_distrib]
    _ = ∏ i : I, ∑ x, Q.w x * F i x := by
          symm
          exact Fintype.prod_sum (fun i x => Q.w x * F i x)

private theorem prod_if_single {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (a : ℝ) : (∏ k : I, if k = i then a else 1) = a := by
  classical
  calc
    (∏ k : I, if k = i then a else 1) = if i = i then a else 1 :=
      Finset.prod_eq_single_of_mem i (Finset.mem_univ _) (by
        intro k hk hki
        by_cases h : k = i
        · exact (hki h).elim
        · simp [h])
    _ = a := by simp

private theorem prod_if_two {I : Type*} [Fintype I] [DecidableEq I]
    (i j : I) (a b : ℝ) (hij : i ≠ j) :
    (∏ k : I, if k = i then a else if k = j then b else 1) = a * b := by
  classical
  have hpoint (k : I) :
      (if k = i then a else if k = j then b else 1) =
        (if k = i then a else 1) * (if k = j then b else 1) := by
    by_cases hki : k = i
    · subst k
      simp [hij]
    · by_cases hkj : k = j
      · subst k
        simp [hij.symm]
      · simp [hki, hkj]
  calc
    (∏ k : I, if k = i then a else if k = j then b else 1) =
        ∏ k : I, (if k = i then a else 1) * (if k = j then b else 1) := by
          apply Finset.prod_congr rfl
          intro k hk
          exact hpoint k
    _ = (∏ k : I, if k = i then a else 1) *
          (∏ k : I, if k = j then b else 1) := Finset.prod_mul_distrib
    _ = a * b := by rw [prod_if_single, prod_if_single]

set_option maxHeartbeats 800000 in
theorem iid_sum_square_expectation {I : Type*} {N M : ℕ}
    [Fintype I] [DecidableEq I] (Q : Law N) (P : Law M) (f : Fin N → Fin M → ℝ) :
    (∑ z : I → Fin N, (∏ i, Q.w (z i)) *
        ∑ y, P.w y * (∑ i, f (z i) y) ^ 2) =
      ∑ y, P.w y * ∑ i : I, ∑ j : I,
        if i = j then ∑ x, Q.w x * (f x y) ^ 2
        else (∑ x, Q.w x * f x y) ^ 2 := by
  classical
  let W (z : I → Fin N) : ℝ := ∏ i, Q.w (z i)
  let C (y : Fin M) (i j k : I) (x : Fin N) : ℝ :=
    if i = j then if k = i then (f x y) ^ 2 else 1
    else if k = i then f x y else if k = j then f x y else 1
  have hprodPair (z : I → Fin N) (y : Fin M) (i j : I) :
      (∏ k : I, C y i j k (z k)) = f (z i) y * f (z j) y := by
    by_cases hij : i = j
    · subst j
      have hsingle : (∏ k : I, C y i i k (z k)) = (f (z i) y) ^ 2 := by
        calc
          (∏ k : I, C y i i k (z k)) =
              ∏ k : I, if k = i then (f (z i) y) ^ 2 else 1 := by
                apply Finset.prod_congr rfl
                intro k hk
                by_cases hki : k = i <;> simp [C, hki]
          _ = (f (z i) y) ^ 2 := prod_if_single i _
      rw [hsingle]
      ring
    · have hprod :
        (∏ k : I, C y i j k (z k)) =
          ∏ k : I, if k = i then f (z i) y else if k = j then f (z j) y else 1 := by
            apply Finset.prod_congr rfl
            intro k hk
            by_cases hki : k = i
            · subst k
              simp [C, hij]
            · by_cases hkj : k = j
              · subst k
                simp [C, hij, Ne.symm hij]
              · simp [C, hij, hki, hkj]
      calc
        (∏ k : I, C y i j k (z k)) =
            (∏ k : I, if k = i then f (z i) y else if k = j then f (z j) y else 1) := hprod
        _ = f (z i) y * f (z j) y :=
              prod_if_two i j (f (z i) y) (f (z j) y) hij
  have hPair (y : Fin M) (i j : I) :
      (∑ z : I → Fin N, W z * (f (z i) y * f (z j) y)) =
        if i = j then ∑ x, Q.w x * (f x y) ^ 2
        else (∑ x, Q.w x * f x y) ^ 2 := by
    calc
      (∑ z : I → Fin N, W z * (f (z i) y * f (z j) y)) =
          ∑ z, W z * ∏ k : I, C y i j k (z k) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [hprodPair]
      _ = ∏ k : I, ∑ x, Q.w x * C y i j k x :=
            pi_product_expectation_prod Q (C y i j)
      _ = if i = j then ∑ x, Q.w x * (f x y) ^ 2
          else (∑ x, Q.w x * f x y) ^ 2 := by
            by_cases hij : i = j
            · subst j
              have hfactor :
                  (∏ k : I, ∑ x, Q.w x * C y i i k x) =
                    ∏ k : I, if k = i then ∑ x, Q.w x * (f x y) ^ 2 else 1 := by
                      apply Finset.prod_congr rfl
                      intro k hk
                      by_cases hki : k = i
                      · subst k
                        simp [C]
                      · simp [C, hki, Q.sum_eq_one]
              rw [hfactor, prod_if_single]
              simp
            · simp only [if_neg hij]
              let m : ℝ := ∑ x, Q.w x * f x y
              have hfactor :
                  (∏ k : I, ∑ x, Q.w x * C y i j k x) =
                    ∏ k : I, if k = i then m else if k = j then m else 1 := by
                      apply Finset.prod_congr rfl
                      intro k hk
                      by_cases hki : k = i
                      · subst k
                        simp [C, hij, m]
                      · by_cases hkj : k = j
                        · subst k
                          simp [C, hij, Ne.symm hij, m]
                        · simp [C, hij, hki, hkj, Q.sum_eq_one, m]
              rw [hfactor, prod_if_two i j m m hij]
              simp [m, pow_two]
  have hSquare (z : I → Fin N) (y : Fin M) :
      (∑ i : I, f (z i) y) ^ 2 =
        ∑ i : I, ∑ j : I, f (z i) y * f (z j) y := by
    rw [pow_two, Finset.sum_mul_sum]
  calc
    (∑ z : I → Fin N, W z * ∑ y, P.w y * (∑ i, f (z i) y) ^ 2) =
        ∑ y, P.w y * ∑ z, W z * (∑ i, f (z i) y) ^ 2 := by
          calc
            (∑ z : I → Fin N, W z * ∑ y, P.w y * (∑ i, f (z i) y) ^ 2) =
                ∑ z, ∑ y, W z * (P.w y * (∑ i, f (z i) y) ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro z hz
                  rw [Finset.mul_sum]
            _ = ∑ y, ∑ z, W z * (P.w y * (∑ i, f (z i) y) ^ 2) := Finset.sum_comm
            _ = ∑ y, P.w y * ∑ z, W z * (∑ i, f (z i) y) ^ 2 := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  calc
                    (∑ z, W z * (P.w y * (∑ i, f (z i) y) ^ 2)) =
                        ∑ z, P.w y * (W z * (∑ i, f (z i) y) ^ 2) := by
                          apply Finset.sum_congr rfl
                          intro z hz
                          ring
                    _ = _ := by rw [Finset.mul_sum]
    _ = ∑ y, P.w y * ∑ i : I, ∑ j : I,
          if i = j then ∑ x, Q.w x * (f x y) ^ 2
          else (∑ x, Q.w x * f x y) ^ 2 := by
            apply Finset.sum_congr rfl
            intro y hy
            congr 1
            calc
              (∑ z, W z * (∑ i, f (z i) y) ^ 2) =
                  ∑ z, W z * ∑ i : I, ∑ j : I, f (z i) y * f (z j) y := by
                    apply Finset.sum_congr rfl
                    intro z hz
                    rw [hSquare]
              _ = ∑ i : I, ∑ j : I, ∑ z, W z * (f (z i) y * f (z j) y) := by
                    calc
                      (∑ z, W z * ∑ i : I, ∑ j : I, f (z i) y * f (z j) y) =
                          ∑ z, ∑ i : I, ∑ j : I, W z * (f (z i) y * f (z j) y) := by
                            apply Finset.sum_congr rfl
                            intro z hz
                            calc
                              W z * ∑ i : I, ∑ j : I, f (z i) y * f (z j) y =
                                  ∑ i : I, W z * ∑ j : I, f (z i) y * f (z j) y := by
                                    rw [Finset.mul_sum]
                              _ = ∑ i : I, ∑ j : I, W z * (f (z i) y * f (z j) y) := by
                                    apply Finset.sum_congr rfl
                                    intro i hi
                                    rw [Finset.mul_sum]
                      _ = ∑ i : I, ∑ z, ∑ j : I, W z * (f (z i) y * f (z j) y) :=
                            Finset.sum_comm
                      _ = ∑ i : I, ∑ j : I, ∑ z, W z * (f (z i) y * f (z j) y) := by
                            apply Finset.sum_congr rfl
                            intro i hi
                            exact Finset.sum_comm
              _ = ∑ i : I, ∑ j : I,
                    if i = j then ∑ x, Q.w x * (f x y) ^ 2
                    else (∑ x, Q.w x * f x y) ^ 2 := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      apply Finset.sum_congr rfl
                      intro j hj
                      exact hPair y i j

end HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer
