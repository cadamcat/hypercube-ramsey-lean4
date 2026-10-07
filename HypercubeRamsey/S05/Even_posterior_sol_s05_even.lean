import HypercubeRamsey.S05.Clock
import HypercubeRamsey.Tools.HeavyTrunc

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000

theorem pr_sum {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) [DecidablePred A] :
    P.pr A = ∑ z, if A z then P.w z else 0 := by
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro z _
  exact PToolsMisc.ite_decidable_irrel (A z) (Classical.propDecidable _) (inferInstance) _ _

theorem map_equiv_weight {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinProb α) (e : α ≃ β) (y : β) :
    (FinProb.map P e).w y = P.w (e.symm y) := by
  change (∑ z, if e z = y then P.w z else 0) = P.w (e.symm y)
  rw [Finset.sum_eq_single (e.symm y)]
  · simp
  · intro z hz hne
    have hzy : e z ≠ y := by
      intro h
      apply hne
      exact e.injective (h.trans (e.apply_symm_apply y).symm)
    simp [hzy]
  · simp

theorem averageCoordinateMarginal_count {N k : ℕ} (P : FinProb (Fin k → Fin N)) (x : Fin N) :
    averageCoordinateMarginal P x =
      ∑ z, P.w z * ((Finset.univ.filter fun i : Fin k => z i = x).card : ℝ) / (k : ℝ) := by
  unfold averageCoordinateMarginal
  simp_rw [pr_sum]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  change ((k : ℝ)⁻¹ * ∑ i : Fin k, if z i = x then P.w z else 0) = _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem marginal_total {N k : ℕ} (P : FinProb (Fin k → Fin N)) (hk : 0 < k) :
    ∑ x, averageCoordinateMarginal P x = 1 := by
  unfold averageCoordinateMarginal
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hcoord (i : Fin k) : ∑ x, P.pr (fun z => z i = x) = 1 := by
    simp_rw [pr_sum]
    rw [Finset.sum_comm]
    have hrow (z : Fin k → Fin N) : (∑ x, if z i = x then P.w z else 0) = P.w z := by
      simp
    simp_rw [hrow]
    exact P.sum_eq_one
  simp_rw [hcoord]
  simp [hk.ne']

theorem marginal_nonneg {N k : ℕ} (P : FinProb (Fin k → Fin N)) (x : Fin N) :
    0 ≤ averageCoordinateMarginal P x := by
  rw [averageCoordinateMarginal_count]
  apply Finset.sum_nonneg
  intro z _
  exact div_nonneg (mul_nonneg (P.nonneg z) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

def arrayCoordEquiv (I : Type*) [Fintype I] (s q : ℕ) :
    I × Fin s × Fin q ≃ Fin (Fintype.card I * (s * q)) :=
  Fintype.equivFinOfCardEq (by simp)

def arrayEquiv (I : Type*) [Fintype I] (s q N : ℕ) :
    (I → Fin s → Fin q → Fin N) ≃ (Fin (Fintype.card I * (s * q)) → Fin N) where
  toFun z j := let e := (arrayCoordEquiv I s q).symm j; z e.1 e.2.1 e.2.2
  invFun z i a b := z (arrayCoordEquiv I s q (i, a, b))
  left_inv z := by
    funext i a b
    simp
  right_inv z := by
    funext j
    simp

theorem card_filter_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (p : β → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun a => p (e a))).card = (Finset.univ.filter p).card := by
  let f : {a : α // p (e a)} ≃ {b : β // p b} := {
    toFun a := ⟨e a.1, a.2⟩
    invFun b := ⟨e.symm b.1, by simpa using b.2⟩
    left_inv a := by apply Subtype.ext; simp
    right_inv b := by apply Subtype.ext; simp }
  simpa only [Fintype.card_subtype] using Fintype.card_congr f

theorem array_marginal_count {I : Type*} [Fintype I] [DecidableEq I] {s q N : ℕ}
    [DecidableEq (Fin (Fintype.card I * (s * q)) → Fin N)]
    (P : FinProb (I → Fin s → Fin q → Fin N)) (x : Fin N) :
    averageCoordinateMarginal (FinProb.map P (arrayEquiv I s q N)) x =
      ∑ z, P.w z * ((Finset.univ.filter fun e : I × Fin s × Fin q => z e.1 e.2.1 e.2.2 = x).card : ℝ) /
        ((Fintype.card I * (s * q) : ℕ) : ℝ) := by
  let e := arrayEquiv I s q N
  rw [averageCoordinateMarginal_count]
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_equiv_weight P (arrayEquiv I s q N)]
  simp only [e, Equiv.symm_apply_apply]
  congr 2
  have hc := (card_filter_equiv (arrayCoordEquiv I s q) (fun i => e z i = x)).symm
  dsimp [e, arrayEquiv] at hc
  simp only [Equiv.symm_apply_apply] at hc
  exact_mod_cast hc

theorem product_density {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (P : FinProb Ω) (M D : ℝ) (hM : 0 ≤ M)
    (hcap : ∀ z, M * P.w z ≤ D) (z : I → Ω) :
    M ^ Fintype.card I * (FinProb.pi (fun _ : I => P)).w z ≤ D ^ Fintype.card I := by
  have heq : M ^ Fintype.card I * (FinProb.pi (fun _ : I => P)).w z =
      ∏ i : I, M * P.w (z i) := by
    rw [FinProb.pi, Finset.prod_mul_distrib]
    simp
  rw [heq]
  calc
    _ ≤ ∏ _i : I, D := Finset.prod_le_prod₀
      (fun i _ => mul_nonneg hM (P.nonneg _)) (fun i _ => hcap _)
    _ = _ := by simp

theorem marginal_set_count {N k : ℕ} (P : FinProb (Fin k → Fin N))
    (S : Fin N → Prop) [DecidablePred S] :
    (∑ x, if S x then averageCoordinateMarginal P x else 0) =
      ∑ z, P.w z * ((Finset.univ.filter fun i : Fin k => S (z i)).card : ℝ) / (k : ℝ) := by
  simp_rw [averageCoordinateMarginal_count]
  have hdist (x : Fin N) :
      (if S x then ∑ z, P.w z * ((Finset.univ.filter fun i : Fin k => z i = x).card : ℝ) / (k : ℝ) else 0) =
      ∑ z, if S x then P.w z * ((Finset.univ.filter fun i : Fin k => z i = x).card : ℝ) / (k : ℝ) else 0 := by
    split_ifs <;> simp
  simp_rw [hdist]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  have hcount : (∑ x, if S x then ((Finset.univ.filter fun i : Fin k => z i = x).card : ℝ) else 0) =
      (Finset.univ.filter fun i : Fin k => S (z i)).card := by
    simp_rw [← Finset.sum_boole]
    have hdist2 (x : Fin N) : (if S x then ∑ i : Fin k, if z i = x then (1 : ℝ) else 0 else 0) =
        ∑ i : Fin k, if S x then (if z i = x then 1 else 0) else 0 := by
      split_ifs <;> simp
    simp_rw [hdist2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hterm (x : Fin N) : (if S x then (if z i = x then (1 : ℝ) else 0) else 0) =
        if z i = x then (if S (z i) then 1 else 0) else 0 := by
      by_cases heq : z i = x
      · subst x
        simp
      · simp [heq]
    simp_rw [hterm]
    simp
  calc
    (∑ x, if S x then P.w z * ((Finset.univ.filter fun i : Fin k => z i = x).card : ℝ) / (k : ℝ) else 0) =
        P.w z * (∑ x, if S x then ((Finset.univ.filter fun i : Fin k => z i = x).card : ℝ) else 0) / (k : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = _ := by rw [hcount]

theorem array_set_count {I : Type*} [Fintype I] [DecidableEq I] {s q N : ℕ}
    [DecidableEq (Fin (Fintype.card I * (s * q)) → Fin N)]
    (P : FinProb (I → Fin s → Fin q → Fin N)) (S : Fin N → Prop) [DecidablePred S] :
    (∑ x, if S x then averageCoordinateMarginal (FinProb.map P (arrayEquiv I s q N)) x else 0) =
      ∑ z, P.w z * ((Finset.univ.filter fun e : I × Fin s × Fin q => S (z e.1 e.2.1 e.2.2)).card : ℝ) /
        ((Fintype.card I * (s * q) : ℕ) : ℝ) := by
  let e := arrayEquiv I s q N
  rw [marginal_set_count]
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_equiv_weight P (arrayEquiv I s q N)]
  simp only [e, Equiv.symm_apply_apply]
  congr 2
  have hc := (card_filter_equiv (arrayCoordEquiv I s q) (fun i => S (e z i))).symm
  dsimp [e, arrayEquiv] at hc
  simp only [Equiv.symm_apply_apply] at hc
  exact_mod_cast hc

theorem count_array_subtype {I J V : Type*} [Fintype I] [Fintype J]
    (M : Finset I) (z : I → J → V) (S : V → Prop) [DecidablePred S] :
    (Finset.univ.filter (fun e : M × J => S (z e.1.1 e.2))).card =
      ∑ i : I, if i ∈ M then (Finset.univ.filter fun j : J => S (z i j)).card else 0 := by
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [← Finset.sum_boole, Fintype.sum_prod_type]
  simp_rw [Finset.sum_boole]
  rw [Finset.univ_eq_attach]
  exact (Finset.sum_attach M (fun i : I => ((Finset.univ.filter fun j : J => S (z i j)).card : ℝ))).trans
    (Finset.sum_ite_mem_eq M _).symm

theorem kept_mass_lower {N k : ℕ} (P : FinProb (Fin k → Fin N)) (hk : 0 < k)
    (prior : Fin N → Prop) (B u v err : ℝ)
    (hprior : ∑ x, (if prior x then averageCoordinateMarginal P x else 0) ≤ u)
    (hheavy : ∑ x ∈ heavyCoordinateSet P B, averageCoordinateMarginal P x ≤ v + err) :
    1 - u - v - err ≤
      ∑ x, (if ¬ prior x ∧ (N : ℝ) * averageCoordinateMarginal P x ≤ Real.exp B then
        averageCoordinateMarginal P x else 0) := by
  have hpoint (x : Fin N) :
      averageCoordinateMarginal P x ≤
        (if prior x then averageCoordinateMarginal P x else 0) +
        (if x ∈ heavyCoordinateSet P B then averageCoordinateMarginal P x else 0) +
        (if ¬ prior x ∧ (N : ℝ) * averageCoordinateMarginal P x ≤ Real.exp B then
          averageCoordinateMarginal P x else 0) := by
    by_cases hp : prior x
    · simp only [hp, if_true, not_true_eq_false, false_and, if_false, add_zero]
      split_ifs <;> linarith [marginal_nonneg P x]
    · by_cases hh : Real.exp B < (N : ℝ) * averageCoordinateMarginal P x
      · simp [hp, heavyCoordinateSet, hh, not_le.mpr hh]
      · simp [hp, heavyCoordinateSet, hh, le_of_not_gt hh]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hpoint x)
  rw [marginal_total P hk, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have heq : (∑ x, if x ∈ heavyCoordinateSet P B then averageCoordinateMarginal P x else 0) =
      ∑ x ∈ heavyCoordinateSet P B, averageCoordinateMarginal P x := by
    rw [← Finset.sum_filter]
    simp
  rw [heq] at hsum
  linarith

theorem normalized_kept_row {N : ℕ} (μ : Fin N → ℝ) (keep : Fin N → Prop)
    (hμ : ∀ x, 0 ≤ μ x) (C B M : ℝ)
    (hC : 0 < C)
    (hmass : C ≤ ∑ x, if keep x then μ x else 0)
    (hcap : ∀ x, keep x → M * μ x ≤ B) (hB : 0 ≤ B) :
    (∀ x, 0 ≤ (if keep x then μ x else 0) / (∑ y, if keep y then μ y else 0)) ∧
    (∑ x, (if keep x then μ x else 0) / (∑ y, if keep y then μ y else 0) = 1) ∧
    (∀ x, M * ((if keep x then μ x else 0) / (∑ y, if keep y then μ y else 0)) ≤ B / C) := by
  have hm : 0 < ∑ y, if keep y then μ y else 0 := hC.trans_le hmass
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact div_nonneg (by split_ifs <;> simp [hμ x]) hm.le
  · rw [← Finset.sum_div, div_self hm.ne']
  · intro x
    rw [← mul_div_assoc]
    by_cases hx : keep x
    · rw [if_pos hx]
      calc
        M * μ x / (∑ y, if keep y then μ y else 0) ≤ B / (∑ y, if keep y then μ y else 0) :=
          div_le_div_of_nonneg_right (hcap x hx) hm.le
        _ ≤ B / C := div_le_div_of_nonneg_left hB hC hmass
    · simp only [if_neg hx, mul_zero, zero_div]
      exact div_nonneg hB hC.le

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

theorem block_density_uniform (H : X.KeyHist) (K : X.Ty) (hK : X.Step2Bounds H K)
    (z : X.Block K) :
    (N : ℝ) ^ (X.p.q0 * X.p.typeSegs n K) * (X.blockLaw H K).w z ≤
      Real.exp ((X.p.Kpp * (1 + ∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ)) +
        (n : ℝ) ^ γ) * (X.p.q0 * X.p.typeSegs n K : ℕ)) := by
  let d := X.p.Kpp * (1 + ∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ))
  let k := X.p.q0 * X.p.typeSegs n K
  have hN : 0 < (N : ℝ) := by exact_mod_cast Fin.pos X.y₀
  have hNpow : 0 < (N : ℝ) ^ k := pow_pos hN _
  have hRef : X.refBlock K z ≤ Real.exp ((n : ℝ) ^ γ * k) / (N : ℝ) ^ k := by
    calc
      X.refBlock K z ≤ ∏ _s : Fin (X.p.typeSegs n K),
          Real.exp ((X.p.q0 : ℝ) * (n : ℝ) ^ γ) / (N : ℝ) ^ X.p.q0 := by
        apply Finset.prod_le_prod₀
        · intro s _
          exact X.S.reference.nonneg (z s)
        · intro s _
          exact X.S.reference_density (z s)
      _ = (Real.exp ((X.p.q0 : ℝ) * (n : ℝ) ^ γ) / (N : ℝ) ^ X.p.q0) ^
          (X.p.typeSegs n K) := by rw [Finset.prod_const]; simp
      _ = Real.exp ((n : ℝ) ^ γ * k) / (N : ℝ) ^ k := by
        rw [div_pow, ← Real.exp_nat_mul, ← pow_mul]
        dsimp [k]
        congr 1
        congr 1
        push_cast
        ring
  have hconst : X.blockConst K ^ k = Real.exp (d * k) := by
    unfold Setup5.blockConst
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [d]
    ring
  calc
    (N : ℝ) ^ k * (X.blockLaw H K).w z ≤
        (N : ℝ) ^ k * (X.blockConst K ^ k * X.refBlock K z) :=
      mul_le_mul_of_nonneg_left (hK.2.1 z) hNpow.le
    _ ≤ (N : ℝ) ^ k * (Real.exp (d * k) *
        (Real.exp ((n : ℝ) ^ γ * k) / (N : ℝ) ^ k)) := by
      rw [hconst]
      gcongr
    _ = Real.exp ((d + (n : ℝ) ^ γ) * k) := by
      rw [show (N : ℝ) ^ k * (Real.exp (d * k) *
          (Real.exp ((n : ℝ) ^ γ * k) / (N : ℝ) ^ k)) =
          Real.exp (d * k) * Real.exp ((n : ℝ) ^ γ * k) by field_simp,
        ← Real.exp_add]
      congr 1
      ring

end
end HypercubeRamsey.Lane_sol_s05_even
