import HypercubeRamsey.S11.Core.Definitions
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.Tools.Ramsey

namespace HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer

open Filter

theorem eventually_pow_gap (a b c : ℝ) (hab : a < b) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a < (n : ℝ) ^ b := by
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hnlarge, htend.eventually_gt_atTop c] with n hn hlarge
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  calc
    c * (n : ℝ) ^ a < (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ b := by rw [← Real.rpow_add hnpos]; congr 1 <;> ring

theorem innerCoord_card_le (n : ℕ) : Fintype.card (InnerCoord n) ≤ hIn n := by
  simpa using Fintype.card_le_of_injective
    (fun j : InnerCoord n => (⟨j.1.val, j.2⟩ : Fin (hIn n)))
    (by
      intro j j' hj
      have hv : j.1.val = j'.1.val := congrArg (fun z : Fin (hIn n) => z.val) hj
      exact Subtype.ext (Fin.ext hv))

theorem hIn_real_le_pow (n : ℕ) :
    (hIn n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := by
  unfold hIn
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem card_lt_ramsey_of_forbidden {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hclique : ∀ C : Finset V, C.card = s →
      ¬ (∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v))
    (hindependent : ∀ I : Finset V, I.card = t →
      ¬ (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v)) :
    Fintype.card V < Nat.choose (s + t - 2) (s - 1) := by
  by_contra h
  have hcard : Nat.choose (s + t - 2) (s - 1) ≤ Fintype.card V := Nat.not_lt.mp h
  rcases HypercubeRamsey.xRamseyBinom G s t hs ht hcard with h | h
  · obtain ⟨C, hCcard, hC⟩ := h
    exact hclique C hCcard hC
  · obtain ⟨I, hIcard, hI⟩ := h
    exact hindependent I hIcard hI

theorem weighted_gram_clique_impossible {V : Type*} [Fintype V] [DecidableEq V]
    {N : ℕ} (s : Finset V) (t : ℕ) (ht : 0 < t) (hcard : s.card = t)
    (π : Fin N → ℝ) (hπ : ∀ y, 0 ≤ π y)
    (f : V → Fin N → ℝ) (hfnorm : ∀ v, (∑ y, π y * (f v y) ^ 2) ≤ 1)
    (g : Fin N → ℝ) (hgnorm : (∑ y, π y * (g y) ^ 2) ≤ 1)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hgap : 1 / (t : ℝ) + ε < τ ^ 2)
    (hcorr : ∀ v ∈ s, ∀ w ∈ s, v ≠ w →
      (∑ y, π y * f v y * f w y) ≤ ε)
    (hproj : ∀ v ∈ s, τ ≤ ∑ y, π y * f v y * g y) : False := by
  classical
  let vbar : Fin N → ℝ := fun y => (t : ℝ)⁻¹ * ∑ v ∈ s, f v y
  let corr : V → V → ℝ := fun v w => ∑ y, π y * f v y * f w y
  have htpos : 0 < (t : ℝ) := by exact_mod_cast ht
  have hcardR : (s.card : ℝ) = t := by exact_mod_cast hcard
  have hprojSum : (∑ v ∈ s, τ) ≤ ∑ v ∈ s, ∑ y, π y * f v y * g y := by
    apply Finset.sum_le_sum
    intro v hv
    exact hproj v hv
  have hprojAvg : τ ≤ ∑ y, π y * vbar y * g y := by
    have hmul : (t : ℝ)⁻¹ * (∑ v ∈ s, τ) ≤
        (t : ℝ)⁻¹ * (∑ v ∈ s, ∑ y, π y * f v y * g y) :=
      mul_le_mul_of_nonneg_left hprojSum (inv_nonneg.mpr htpos.le)
    have hconst : (∑ v ∈ s, τ) = (t : ℝ) * τ := by
      simp [Finset.sum_const, hcard]
    have hinter :
        (t : ℝ)⁻¹ * (∑ v ∈ s, ∑ y, π y * f v y * g y) =
          ∑ y, π y * vbar y * g y := by
      dsimp [vbar]
      calc
        (t : ℝ)⁻¹ * (∑ v ∈ s, ∑ y, π y * f v y * g y) =
            ∑ v ∈ s, ∑ y, (t : ℝ)⁻¹ * (π y * f v y * g y) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v hv
          rw [Finset.mul_sum]
        _ = ∑ y, ∑ v ∈ s, (t : ℝ)⁻¹ * (π y * f v y * g y) := by
          rw [Finset.sum_comm]
        _ = ∑ y, π y * ((t : ℝ)⁻¹ * ∑ v ∈ s, f v y) * g y := by
          apply Finset.sum_congr rfl
          intro y hy
          calc
            (∑ v ∈ s, (t : ℝ)⁻¹ * (π y * f v y * g y)) =
                (t : ℝ)⁻¹ * ∑ v ∈ s, π y * f v y * g y := by rw [Finset.mul_sum]
            _ = π y * ((t : ℝ)⁻¹ * ∑ v ∈ s, f v y) * g y := by
              calc
                (t : ℝ)⁻¹ * ∑ v ∈ s, π y * f v y * g y =
                    (t : ℝ)⁻¹ * (π y * g y * ∑ v ∈ s, f v y) := by
                  congr 1
                  calc
                    (∑ v ∈ s, π y * f v y * g y) =
                        ∑ v ∈ s, (π y * g y) * f v y := by
                      apply Finset.sum_congr rfl
                      intro v hv
                      ring
                    _ = (π y * g y) * ∑ v ∈ s, f v y := by rw [Finset.mul_sum]
                _ = π y * ((t : ℝ)⁻¹ * ∑ v ∈ s, f v y) * g y := by ring
        _ = ∑ y, π y * vbar y * g y := by rfl
    calc
      τ = (t : ℝ)⁻¹ * (∑ v ∈ s, τ) := by rw [hconst]; field_simp [htpos.ne']
      _ ≤ (t : ℝ)⁻¹ * (∑ v ∈ s, ∑ y, π y * f v y * g y) := hmul
      _ = ∑ y, π y * vbar y * g y := hinter
  have hnormEq : (∑ y, π y * (vbar y) ^ 2) =
      (t : ℝ)⁻¹ ^ 2 * (∑ v ∈ s, ∑ w ∈ s, corr v w) := by
    dsimp [vbar, corr]
    calc
      (∑ y, π y * ((t : ℝ)⁻¹ * ∑ v ∈ s, f v y) ^ 2) =
          ∑ y, ((t : ℝ)⁻¹) ^ 2 * (π y * (∑ v ∈ s, f v y) ^ 2) := by
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = ((t : ℝ)⁻¹) ^ 2 * ∑ y, π y * (∑ v ∈ s, f v y) ^ 2 := by
        rw [Finset.mul_sum]
      _ = ((t : ℝ)⁻¹) ^ 2 *
          ∑ y, π y * ((∑ v ∈ s, f v y) * (∑ w ∈ s, f w y)) := by
        apply congrArg
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = ((t : ℝ)⁻¹) ^ 2 *
          ∑ y, π y * ∑ v ∈ s, ∑ w ∈ s, f v y * f w y := by
        congr 1
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.sum_mul_sum]
      _ = ((t : ℝ)⁻¹) ^ 2 *
          ∑ v ∈ s, ∑ w ∈ s, ∑ y, π y * f v y * f w y := by
        congr 1
        simp_rw [Finset.mul_sum]
        calc
          (∑ y, ∑ v ∈ s, ∑ w ∈ s, π y * (f v y * f w y)) =
              ∑ v ∈ s, ∑ y, ∑ w ∈ s, π y * (f v y * f w y) := by
            rw [Finset.sum_comm]
          _ = ∑ v ∈ s, ∑ w ∈ s, ∑ y, π y * f v y * f w y := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro w hw
            apply Finset.sum_congr rfl
            intro y hy
            ring
  have hdiag : (∑ v ∈ s, corr v v) ≤ t := by
    calc
      (∑ v ∈ s, corr v v) ≤ ∑ v ∈ s, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        dsimp [corr]
        simpa [pow_two, mul_assoc] using hfnorm v
      _ = (s.card : ℝ) := by simp
      _ = t := hcardR
  have hoff (v : V) (hv : v ∈ s) :
      (∑ w ∈ s.erase v, corr v w) ≤ (t : ℝ) * ε := by
    calc
      (∑ w ∈ s.erase v, corr v w) ≤ ∑ w ∈ s.erase v, ε := by
        apply Finset.sum_le_sum
        intro w hw
        have hne : v ≠ w := by
          intro h
          subst w
          simp at hw
        exact hcorr v hv w (Finset.mem_of_mem_erase hw) hne
      _ = ((s.erase v).card : ℝ) * ε := by simp
      _ ≤ (t : ℝ) * ε := by
        have hcardErase : (s.erase v).card ≤ s.card := Finset.card_erase_le
        have hcardEraseR : ((s.erase v).card : ℝ) ≤ (t : ℝ) := by
          calc
            ((s.erase v).card : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hcardErase
            _ = t := hcardR
        exact mul_le_mul_of_nonneg_right hcardEraseR hε
  have hoffAll : (∑ v ∈ s, ∑ w ∈ s.erase v, corr v w) ≤ (t : ℝ) ^ 2 * ε := by
    calc
      (∑ v ∈ s, ∑ w ∈ s.erase v, corr v w) ≤ ∑ v ∈ s, (t : ℝ) * ε := by
        apply Finset.sum_le_sum
        intro v hv
        exact hoff v hv
      _ = (s.card : ℝ) * ((t : ℝ) * ε) := by simp
      _ = (t : ℝ) ^ 2 * ε := by rw [hcardR]; ring
  have hpair : (∑ v ∈ s, ∑ w ∈ s, corr v w) =
      (∑ v ∈ s, corr v v) + (∑ v ∈ s, ∑ w ∈ s.erase v, corr v w) := by
    calc
      (∑ v ∈ s, ∑ w ∈ s, corr v w) =
          ∑ v ∈ s, (corr v v + ∑ w ∈ s.erase v, corr v w) := by
        apply Finset.sum_congr rfl
        intro v hv
        have h := Finset.sum_erase_add s (fun w => corr v w) hv
        linarith
      _ = (∑ v ∈ s, corr v v) + ∑ v ∈ s, ∑ w ∈ s.erase v, corr v w :=
        Finset.sum_add_distrib
  have hnormV : (∑ y, π y * (vbar y) ^ 2) ≤ 1 / (t : ℝ) + ε := by
    rw [hnormEq, hpair]
    have htinv : 0 ≤ ((t : ℝ)⁻¹) ^ 2 := sq_nonneg _
    calc
      ((t : ℝ)⁻¹) ^ 2 *
          ((∑ v ∈ s, corr v v) + ∑ v ∈ s, ∑ w ∈ s.erase v, corr v w) ≤
        ((t : ℝ)⁻¹) ^ 2 * ((t : ℝ) + (t : ℝ) ^ 2 * ε) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hdiag hoffAll) htinv
      _ = 1 / (t : ℝ) + ε := by
        field_simp [htpos.ne']
  let F' : Fin N → ℝ := fun y => Real.sqrt (π y) * vbar y
  let G' : Fin N → ℝ := fun y => Real.sqrt (π y) * g y
  have hsumFG : (∑ y, F' y * G' y) = ∑ y, π y * vbar y * g y := by
    apply Finset.sum_congr rfl
    intro y hy
    dsimp [F', G']
    calc
      Real.sqrt (π y) * vbar y * (Real.sqrt (π y) * g y) =
          (Real.sqrt (π y)) ^ 2 * (vbar y * g y) := by ring
      _ = π y * (vbar y * g y) := by rw [Real.sq_sqrt (hπ y)]
      _ = π y * vbar y * g y := by ring
  have hsumFF : (∑ y, F' y ^ 2) = ∑ y, π y * (vbar y) ^ 2 := by
    apply Finset.sum_congr rfl
    intro y hy
    dsimp [F']
    calc
      (Real.sqrt (π y) * vbar y) ^ 2 =
          (Real.sqrt (π y)) ^ 2 * (vbar y) ^ 2 := by ring
      _ = π y * (vbar y) ^ 2 := by rw [Real.sq_sqrt (hπ y)]
  have hsumGG : (∑ y, G' y ^ 2) = ∑ y, π y * (g y) ^ 2 := by
    apply Finset.sum_congr rfl
    intro y hy
    dsimp [G']
    calc
      (Real.sqrt (π y) * g y) ^ 2 =
          (Real.sqrt (π y)) ^ 2 * (g y) ^ 2 := by ring
      _ = π y * (g y) ^ 2 := by rw [Real.sq_sqrt (hπ y)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N)) F' G'
  rw [hsumFG, hsumFF, hsumGG] at hCS
  have hnormNonneg : 0 ≤ ∑ y, π y * (vbar y) ^ 2 :=
    Finset.sum_nonneg fun y hy => mul_nonneg (hπ y) (sq_nonneg _)
  have hprojSq : (∑ y, π y * vbar y * g y) ^ 2 ≤ ∑ y, π y * (vbar y) ^ 2 := by
    calc
      (∑ y, π y * vbar y * g y) ^ 2 ≤
          (∑ y, π y * (vbar y) ^ 2) * (∑ y, π y * (g y) ^ 2) := hCS
      _ ≤ (∑ y, π y * (vbar y) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hgnorm hnormNonneg
      _ = ∑ y, π y * (vbar y) ^ 2 := by ring
  have hτV : τ ^ 2 ≤ ∑ y, π y * (vbar y) ^ 2 := by
    have hprojNonneg : 0 ≤ ∑ y, π y * vbar y * g y := le_trans hτ.le hprojAvg
    nlinarith [hprojSq, hprojAvg]
  have hgap' : τ ^ 2 ≤ 1 / (t : ℝ) + ε := hτV.trans hnormV
  linarith [hgap, hgap']

end HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer
