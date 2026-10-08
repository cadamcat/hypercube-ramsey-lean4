import HypercubeRamsey.S05.Even_posterior_sol_s05_even
import HypercubeRamsey.S05.History_q_s05_h5l

namespace HypercubeRamsey.Lane_sol_s05_even
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

/-- Separate two independent fields at each ID into their two global product laws. -/
def piProdEquiv {I A B : Type*} : (I → A × B) ≃ ((I → A) × (I → B)) where
  toFun ω := (fun i => (ω i).1, fun i => (ω i).2)
  invFun ab := fun i => (ab.1 i, ab.2 i)
  left_inv ω := by funext i; exact Prod.eta _
  right_inv ab := by cases ab; rfl

theorem pi_prod_expect {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
    (P : I → FinProb A) (Q : I → FinProb B) (f : (I → A × B) → ℝ) :
    (FinProb.pi (fun i => (P i).prod (Q i))).expect f =
      (FinProb.pi P).expect (fun a => (FinProb.pi Q).expect (fun b => f (fun i => (a i, b i)))) := by
  unfold FinProb.expect
  rw [← Equiv.sum_comp (piProdEquiv (I := I) (A := A) (B := B)).symm]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change (∏ i, (P i).w (a i) * (Q i).w (b i)) * f (fun i => (a i, b i)) =
    (∏ i, (P i).w (a i)) * ((∏ i, (Q i).w (b i)) * f (fun i => (a i, b i)))
  rw [Finset.prod_mul_distrib]
  ring

/-- Iid whole blocks retain the block's average marginal. -/
theorem iid_array_empirical_mean {I J V : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [Fintype V] [DecidableEq V] (P : FinProb (J → V)) (x : V) (hI : 0 < Fintype.card I)
    (hJ : 0 < Fintype.card J) :
    (FinProb.pi (fun _ : I => P)).expect (fun z =>
      ((Finset.univ.filter fun e : I × J => z e.1 e.2 = x).card : ℝ) /
        ((Fintype.card I * Fintype.card J : ℕ) : ℝ)) =
      (Fintype.card J : ℝ)⁻¹ *
        ∑ z, P.w z * ((Finset.univ.filter fun j : J => z j = x).card : ℝ) := by
  have hc (z : I → J → V) :
      ((Finset.univ.filter fun e : I × J => z e.1 e.2 = x).card : ℝ) =
        ∑ i : I, ((Finset.univ.filter fun j : J => z i j = x).card : ℝ) := by
    simp_rw [← Finset.sum_boole]
    rw [Fintype.sum_prod_type]
  simp_rw [hc]
  unfold FinProb.expect
  simp_rw [Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hmean (i : I) :
      (∑ z : I → J → V, (FinProb.pi (fun _ : I => P)).w z *
        (((Finset.univ.filter fun j : J => z i j = x).card : ℝ) /
          ((Fintype.card I * Fintype.card J : ℕ) : ℝ))) =
      ∑ z, P.w z * (((Finset.univ.filter fun j : J => z j = x).card : ℝ) /
          ((Fintype.card I * Fintype.card J : ℕ) : ℝ)) := by
    simpa only [FinProb.expect] using Lane_q_s05_h5l.pi_expect_singleton5 (fun _ : I => P) i
      (fun z => ((Finset.univ.filter fun j : J => z j = x).card : ℝ) /
        ((Fintype.card I * Fintype.card J : ℕ) : ℝ)) (fun _ : J => x)
  simp_rw [hmean]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  have hIR : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  have hJR : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  field_simp

end
end HypercubeRamsey.Lane_sol_s05_even
