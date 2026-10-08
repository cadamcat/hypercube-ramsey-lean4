import HypercubeRamsey.S05.Even_load_axes_sol_s05_even
import HypercubeRamsey.S05.Even_refs_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

theorem iid_block_empirical_mean {I J B V : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [Fintype B] [Fintype V] [DecidableEq V] (P : FinProb B) (eval : B → J → V) (b₀ : B) (x : V) (hI : 0 < Fintype.card I)
    (hJ : 0 < Fintype.card J) :
    (FinProb.pi (fun _ : I => P)).expect (fun z =>
      ((Finset.univ.filter fun e : I × J => eval (z e.1) e.2 = x).card : ℝ) /
        ((Fintype.card I * Fintype.card J : ℕ) : ℝ)) =
      (Fintype.card J : ℝ)⁻¹ *
        ∑ z, P.w z * ((Finset.univ.filter fun j : J => eval z j = x).card : ℝ) := by
  have hc (z : I → B) :
      ((Finset.univ.filter fun e : I × J => eval (z e.1) e.2 = x).card : ℝ) =
        ∑ i : I, ((Finset.univ.filter fun j : J => eval (z i) j = x).card : ℝ) := by
    simp_rw [← Finset.sum_boole]
    rw [Fintype.sum_prod_type]
  simp_rw [hc]
  unfold FinProb.expect
  simp_rw [Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hmean (i : I) :
      (∑ z : I → B, (FinProb.pi (fun _ : I => P)).w z *
        (((Finset.univ.filter fun j : J => eval (z i) j = x).card : ℝ) /
          ((Fintype.card I * Fintype.card J : ℕ) : ℝ))) =
      ∑ z, P.w z * (((Finset.univ.filter fun j : J => eval z j = x).card : ℝ) /
          ((Fintype.card I * Fintype.card J : ℕ) : ℝ)) := by
    simpa only [FinProb.expect] using Lane_q_s05_h5l.pi_expect_singleton5 (fun _ : I => P) i
      (fun z => ((Finset.univ.filter fun j : J => eval z j = x).card : ℝ) /
        ((Fintype.card I * Fintype.card J : ℕ) : ℝ)) b₀
  simp_rw [hmean]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  have hIR : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  have hJR : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  field_simp

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

def arrayEmpirical (K : X.Ty) (a : X.Array K) (x : Fin N) : ℝ :=
  ((Finset.univ.filter fun e : Fin (X.p.typeBlocks n K) × Fin (X.p.typeSegs n K) × Fin X.p.q0 =>
    a e.1 e.2.1 e.2.2 = x).card : ℝ) /
      ((X.p.typeBlocks n K * (X.p.q0 * X.p.typeSegs n K) : ℕ) : ℝ)

theorem arrayEmpirical_mean (H : X.KeyHist) (K : X.Ty) (x : Fin N)
    (hB : 0 < X.p.typeBlocks n K) (hS : 0 < X.p.typeSegs n K) :
    (FinProb.pi (fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K)).expect
      (fun a => arrayEmpirical X K a x) = X.avgMarg H K x := by
  have hh := iid_block_empirical_mean (I := Fin (X.p.typeBlocks n K))
    (J := Fin (X.p.typeSegs n K) × Fin X.p.q0) (X.blockLaw H K)
    (fun z e => z e.1 e.2) (fun _ _ => X.y₀) x
    (by simpa using hB) (by simpa using Nat.mul_pos hS X.p.hq0.1)
  simpa only [arrayEmpirical, Setup5.avgMarg, Fintype.card_fin, Fintype.card_prod,
    Nat.mul_comm] using hh

theorem arrayEmpirical_nonneg (K : X.Ty) (a : X.Array K) (x : Fin N) :
    0 ≤ arrayEmpirical X K a x := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem prior_light_bound (H : X.KeyHist) (K : X.Ty) (x : Fin N) (hx : ¬ X.PriorHeavy H K x) :
    (N : ℝ) * X.avgMarg H K x ≤ X.blockConst K ^ X.p.KB := le_of_not_gt hx

end
end HypercubeRamsey.Lane_sol_s05_even
