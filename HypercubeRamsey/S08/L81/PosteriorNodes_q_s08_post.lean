import HypercubeRamsey.S08.L81.SelectionNodes
import HypercubeRamsey.S03.Clock.Leaves_p_clock_r2

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

namespace Lane_q_s08_post

theorem pi_pr_cylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (S : Finset ι)
    (a : ∀ i : {i // i ∈ S}, Ω i.1) :
    (FinProb.pi P).pr (fun ω => ∀ i : {i // i ∈ S}, ω i.1 = a i) =
      ∏ i : {i // i ∈ S}, (P i.1).w (a i) := by
  classical
  let proj : (∀ i, Ω i) → (∀ i : {i // i ∈ S}, Ω i.1) := fun ω i => ω i.1
  have hpr :
      (FinProb.pi P).pr (fun ω => ∀ i : {i // i ∈ S}, ω i.1 = a i) =
        (FinProb.map (FinProb.pi P) proj).w a := by
    unfold FinProb.pr FinProb.map
    apply Finset.sum_congr rfl
    intro ω hω
    have hiff : (∀ i : {i // i ∈ S}, ω i.1 = a i) ↔ proj ω = a := by
      constructor
      · intro h
        funext i
        exact h i
      · intro h i
        exact congrFun h i
    by_cases hfix : ∀ i : {i // i ∈ S}, ω i.1 = a i
    · have heq : proj ω = a := by
        exact hiff.mp hfix
      simp only [if_pos hfix, if_pos heq]
    · have hneq : proj ω ≠ a := by
        intro heq
        exact hfix (hiff.mpr heq)
      simp only [if_neg hfix, if_neg hneq]
  rw [hpr, FinProb.pi_marginal]
  simp [FinProb.pi]

theorem pi_pr_le_fixed {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (S : Finset ι)
    (a : ∀ i : {i // i ∈ S}, Ω i.1) (A : (∀ i, Ω i) → Prop)
    (hA : ∀ ω, A ω → ∀ i : {i // i ∈ S}, ω i.1 = a i) :
    (FinProb.pi P).pr A ≤ ∏ i : {i // i ∈ S}, (P i.1).w (a i) := by
  classical
  calc
    (FinProb.pi P).pr A ≤
        (FinProb.pi P).pr (fun ω => ∀ i : {i // i ∈ S}, ω i.1 = a i) := by
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro ω hω
      by_cases h : A ω
      · have hc : ∀ i : {i // i ∈ S}, ω i.1 = a i := hA ω h
        simp [h, hc]
      · simp only [if_neg h]
        by_cases hc : ∀ i : {i // i ∈ S}, ω i.1 = a i
        · simp only [if_pos hc]
          exact (FinProb.pi P).nonneg ω
        · simp only [if_neg hc]
          norm_num
    _ = ∏ i : {i // i ∈ S}, (P i.1).w (a i) :=
      pi_pr_cylinder P S a

theorem positive_tilt_gate {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (Θ : D.Hist) (g : D.KeyT) (i : D.M.ι)
    (hbase : D.BaseGates Θ g) (hpos : 0 < (D.tilt Θ g).w i) :
    D.GateOpen Θ g i := by
  have hAG : 0 < D.AG g := by
    unfold Ctx.AG
    exact inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) _)
  have hZ : 0 < D.ZG Θ g := by
    have hgate := hbase.2.1.1
    exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8 / 10) hAG) hgate
  have hnum : 0 < D.tiltW Θ g i := by
    unfold Ctx.tilt normOr at hpos
    change 0 < (if (∑ i', D.tiltW Θ g i') = 0 then D.tagLaw.w i else
      D.tiltW Θ g i / ∑ i', D.tiltW Θ g i') at hpos
    have hsumpos : 0 < ∑ i', D.tiltW Θ g i' := by
      simpa [Ctx.ZG] using hZ
    rw [if_neg (ne_of_gt hsumpos)] at hpos
    by_contra hn
    have hle : D.tiltW Θ g i ≤ 0 := le_of_not_gt hn
    have hquot : D.tiltW Θ g i / D.ZG Θ g ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hle hZ.le
    exact (not_le_of_gt hpos) (by simpa [Ctx.ZG] using hquot)
  by_contra hgate
  unfold Ctx.tiltW at hnum
  simp [hgate] at hnum

theorem anchor_miss_le {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (hn : 1 ≤ D.n) (Θ : D.Hist) (g : D.KeyT) (i : D.M.ι)
    (ξ : D.Tup) (j : Fin h)
    (htrue : D.GateOpen Θ g i)
    (hcand : D.GateOpen (Function.update Θ g ξ) g i) :
    (D.anchorU Θ g i).pr (fun x => ¬ Hits D.E D.G x (ξ j)) ≤ D.Δ / (1 - D.Δ) := by
  classical
  have hnR : 0 < (D.n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  have hpow : 0 < (D.n : ℝ) ^ (p / 2) := Real.rpow_pos_of_pos hnR _
  have hΔpos : 0 < D.Δ := Real.exp_pos _
  have hΔlt : D.Δ < 1 := by
    unfold Ctx.Δ
    have hlt : Real.exp (-((D.n : ℝ) ^ (p / 2))) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (neg_neg_of_pos hpow)
    simpa using hlt
  have hfactor : 0 < 1 - D.Δ := sub_pos.mpr hΔlt
  have hcut : 0 < D.cut := Real.exp_pos _
  have hdmpos : 0 < D.dMinus Θ g i := lt_of_lt_of_le hcut htrue.1
  have hdptrue : 0 < D.dPlus Θ g i := by
    have hineq := htrue.2
    have hprod : 0 < (1 - D.Δ) * D.dMinus Θ g i := mul_pos hfactor hdmpos
    exact lt_of_lt_of_le hprod hineq
  have hcross_update (x : Fin D.N) :
      D.crossHit (Function.update Θ g ξ) g x ↔ D.crossHit Θ g x := by
    constructor
    · intro hx u hu
      have hne : u ≠ g := by
        intro heq
        subst u
        have hdist : keyDist g g = 0 := by simp [keyDist]
        have hu' : keyDist g g = 1 := by simpa [crossKeys] using hu
        rw [hdist] at hu'
        norm_num at hu'
      have hval : (Function.update Θ g ξ) u = Θ u := Function.update_of_ne hne ξ Θ
      simpa [hval] using hx u hu
    · intro hx u hu
      have hne : u ≠ g := by
        intro heq
        subst u
        have hdist : keyDist g g = 0 := by simp [keyDist]
        have hu' : keyDist g g = 1 := by simpa [crossKeys] using hu
        rw [hdist] at hu'
        norm_num at hu'
      have hval : (Function.update Θ g ξ) u = Θ u := Function.update_of_ne hne ξ Θ
      simpa [hval] using hx u hu
  have hown_update (x : Fin D.N) :
      D.ownHit (Function.update Θ g ξ) g x ↔ D.crossHit Θ g x ∧ D.hitsAll x ξ := by
    simp [Ctx.ownHit, Ctx.hitsAll, hcross_update, Function.update]
  have hdmEq : D.dMinus (Function.update Θ g ξ) g i = D.dMinus Θ g i := by
    unfold Ctx.dMinus
    apply Finset.sum_congr rfl
    intro x hx
    simp only [hcross_update]
  have hdpCand : (1 - D.Δ) * D.dMinus Θ g i ≤
      D.dPlus (Function.update Θ g ξ) g i := by
    simpa [hdmEq] using hcand.2
  have hmass_miss_le :
      (∑ x, (D.M.μ i).w x *
        if D.crossHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0) ≤
        D.dMinus Θ g i - D.dPlus (Function.update Θ g ξ) g i := by
    unfold Ctx.dMinus Ctx.dPlus
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro x hx
    by_cases hcross : D.crossHit Θ g x
    · by_cases hall : D.hitsAll x ξ
      · have hj : Hits D.E D.G x (ξ j) := hall j
        simp [hcross, hall, hj, hown_update]
      · have hnotown : ¬ D.ownHit (Function.update Θ g ξ) g x := by
          rw [hown_update]
          simp [hcross, hall]
        by_cases hmiss : ¬ Hits D.E D.G x (ξ j)
        · simp [hcross, hmiss, hnotown, (D.M.μ i).nonneg x]
        · simp [hcross, hmiss, hnotown]
          exact (D.M.μ i).nonneg x
    · have hnotown : ¬ D.ownHit (Function.update Θ g ξ) g x := by
        rw [hown_update]
        simp [hcross]
      simp [hcross, hnotown]
  have hmissmass :
      (∑ x, (D.M.μ i).w x *
        if D.ownHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0) ≤
        (∑ x, (D.M.μ i).w x *
          if D.crossHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0) := by
    apply Finset.sum_le_sum
    intro x hx
    have hown : D.ownHit Θ g x → D.crossHit Θ g x := fun ho => ho.1
    by_cases hbad : D.ownHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j)
    · have hbad' : D.crossHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) := ⟨hown hbad.1, hbad.2⟩
      simp [hbad, hbad']
    · by_cases hcross : D.crossHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j)
      · have hnotown : ¬ D.ownHit Θ g x := by
          intro ho
          exact hbad ⟨ho, hcross.2⟩
        simp [hbad, hcross, hnotown]
        exact (D.M.μ i).nonneg x
      · simp [hbad, hcross]
  have hnumBound :
      (∑ x, (D.M.μ i).w x *
        if D.ownHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0) ≤
        D.Δ * D.dMinus Θ g i := by
    calc
      _ ≤ ∑ x, (D.M.μ i).w x *
            if D.crossHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0 := hmissmass
      _ ≤ D.dMinus Θ g i - D.dPlus (Function.update Θ g ξ) g i := hmass_miss_le
      _ ≤ D.dMinus Θ g i - (1 - D.Δ) * D.dMinus Θ g i := by linarith [hdpCand]
      _ = D.Δ * D.dMinus Θ g i := by ring
  have hprob : (D.anchorU Θ g i).pr (fun x => ¬ Hits D.E D.G x (ξ j)) =
      (∑ x, (D.M.μ i).w x *
        if D.ownHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0) /
        D.dPlus Θ g i := by
    have hden : (∑ x, (D.M.μ i).w x * if D.ownHit Θ g x then 1 else 0) =
        D.dPlus Θ g i := rfl
    have hdenpos : 0 < ∑ x, (D.M.μ i).w x * if D.ownHit Θ g x then 1 else 0 := by
      simpa [Ctx.dPlus] using hdptrue
    simp only [FinProb.pr, Ctx.anchorU, normOr]
    simp only [if_neg (ne_of_gt hdenpos)]
    simp_rw [hden]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hm : ¬ Hits D.E D.G x (ξ j) <;>
      by_cases ho : D.ownHit Θ g x <;> simp [hm, ho] <;> ring
  rw [hprob]
  apply (div_le_iff₀ hdptrue).2
  calc
    (∑ x, (D.M.μ i).w x *
      if D.ownHit Θ g x ∧ ¬ Hits D.E D.G x (ξ j) then 1 else 0) ≤
        D.Δ * D.dMinus Θ g i := hnumBound
    _ ≤ (D.Δ / (1 - D.Δ)) * D.dPlus Θ g i := by
      calc
        D.Δ * D.dMinus Θ g i =
            (D.Δ / (1 - D.Δ)) * ((1 - D.Δ) * D.dMinus Θ g i) := by
          field_simp [ne_of_gt hfactor]
        _ ≤ (D.Δ / (1 - D.Δ)) * D.dPlus Θ g i :=
          mul_le_mul_of_nonneg_left htrue.2 (div_nonneg hΔpos.le hfactor.le)

end Lane_q_s08_post

theorem avgMarg_nonneg {N k : ℕ} (Q : FinProb (Fin k → Fin N)) (y : Fin N) :
    0 ≤ averageCoordinateMarginal Q y := by
  unfold averageCoordinateMarginal
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k))
  apply Finset.sum_nonneg
  intro j hj
  exact pr_nonneg Q (fun ξ => ξ j = y)

theorem avgMarg_sum_one {N k : ℕ} (Q : FinProb (Fin k → Fin N)) (hk : 0 < k) :
    ∑ y : Fin N, averageCoordinateMarginal Q y = 1 := by
  classical
  have hprob (j : Fin k) (y : Fin N) : Q.pr (fun ξ => ξ j = y) =
      (FinProb.map Q (fun ξ => ξ j)).w y := by
    unfold FinProb.pr FinProb.map
    apply Finset.sum_congr rfl
    intro ξ hξ
    exact PToolsMisc.ite_decidable_irrel (ξ j = y) (Classical.propDecidable _)
      (inferInstance : Decidable (ξ j = y)) _ _
  have hcoord (j : Fin k) : ∑ y : Fin N, Q.pr (fun ξ => ξ j = y) = 1 := by
    calc
      ∑ y : Fin N, Q.pr (fun ξ => ξ j = y) =
          ∑ y : Fin N, (FinProb.map Q (fun ξ => ξ j)).w y := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hprob j y
      _ = 1 := (FinProb.map Q (fun ξ => ξ j)).sum_eq_one
  unfold averageCoordinateMarginal
  rw [← Finset.mul_sum, Finset.sum_comm]
  calc
    (k : ℝ)⁻¹ * ∑ j : Fin k, ∑ y : Fin N, Q.pr (fun ξ => ξ j = y) =
        (k : ℝ)⁻¹ * ∑ j : Fin k, 1 := by
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          exact hcoord j
    _ = 1 := by simp [hk.ne']

theorem avgMarg_ne_zero_support {N k : ℕ} (Q : FinProb (Fin k → Fin N)) (y : Fin N)
    (hQ : averageCoordinateMarginal Q y ≠ 0) :
    ∃ ξ j, Q.w ξ ≠ 0 ∧ ξ j = y := by
  classical
  have hsum : (∑ j : Fin k, Q.pr (fun ξ => ξ j = y)) ≠ 0 := by
    intro hs
    apply hQ
    simp [averageCoordinateMarginal, hs]
  have hj : ∃ j : Fin k, Q.pr (fun ξ => ξ j = y) ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hsum
    apply Finset.sum_eq_zero
    intro j hj
    exact hn j
  obtain ⟨j, hj⟩ := hj
  have hξ : ∃ ξ, ξ j = y ∧ Q.w ξ ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hj
    unfold FinProb.pr
    apply Finset.sum_eq_zero
    intro ξ hξ
    by_cases hxy : ξ j = y
    · have hw : Q.w ξ = 0 := hn ξ hxy
      simp [hxy, hw]
    · simp [hxy]
  obtain ⟨ξ, hxy, hw⟩ := hξ
  exact ⟨ξ, j, hw, hxy⟩

private theorem basePost_pos_fcand_pos {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist) (c : D.CellT) (π : D.Pres c.1) (ξ : D.Tup)
    (hM : 0 < D.Mden Θ c.1 (D.obsOf π))
    (hq : 0 < (D.basePost Θ c.1 (D.obsOf π)).w ξ) :
    0 < D.Fcand Θ c.1 ξ (D.obsOf π) := by
  have hsum : ∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π) =
      D.Mden Θ c.1 (D.obsOf π) := rfl
  have hden : 0 < ∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π) := by
    simpa [hsum] using hM
  change 0 < (if ∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π) = 0 then
      D.R'.w ξ else
      D.R'.w ξ * D.Fcand Θ c.1 ξ (D.obsOf π) /
        ∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π)) at hq
  rw [if_neg (ne_of_gt hden)] at hq
  have hprod : 0 < D.R'.w ξ * D.Fcand Θ c.1 ξ (D.obsOf π) := by
    by_contra hnot
    have hle : D.R'.w ξ * D.Fcand Θ c.1 ξ (D.obsOf π) ≤ 0 := le_of_not_gt hnot
    have hinv : 0 ≤ (∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π))⁻¹ :=
      (inv_pos.mpr hden).le
    have hmul : D.R'.w ξ * D.Fcand Θ c.1 ξ (D.obsOf π) *
        (∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π))⁻¹ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hinv
    have hpositive : 0 < D.R'.w ξ * D.Fcand Θ c.1 ξ (D.obsOf π) *
        (∑ ξ', D.R'.w ξ' * D.Fcand Θ c.1 ξ' (D.obsOf π))⁻¹ := by
      simpa [div_eq_mul_inv] using hq
    exact (not_le_of_gt hpositive) hmul
  have hR : 0 ≤ D.R'.w ξ := D.R'.nonneg ξ
  have hF : 0 ≤ D.Fcand Θ c.1 ξ (D.obsOf π) := D.Fcand_nonneg Θ c.1 ξ (D.obsOf π)
  by_contra hnot
  have hF' : D.Fcand Θ c.1 ξ (D.obsOf π) ≤ 0 := le_of_not_gt hnot
  have hmul : D.R'.w ξ * D.Fcand Θ c.1 ξ (D.obsOf π) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hR hF'
  exact (not_le_of_gt hprod) hmul

theorem selPost_pos_fcand_pos {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist) (P : D.Pos) (c : D.CellT) (π : D.Pres c.1) (ξ : D.Tup)
    (hM : 0 < D.Mden Θ c.1 (D.obsOf π))
    (hG : D.Gsel Θ P c ξ π ≤ D.Fcand Θ c.1 ξ (D.obsOf π))
    (hq : 0 < (D.selPost Θ P c π).w ξ) :
    0 < D.Fcand Θ c.1 ξ (D.obsOf π) := by
  classical
  have hbase : 0 < (D.basePost Θ c.1 (D.obsOf π)).w ξ →
      0 < D.Fcand Θ c.1 ξ (D.obsOf π) :=
    basePost_pos_fcand_pos D Θ c π ξ hM
  unfold Ctx.selPost at hq
  split_ifs at hq with hadj
  · let f : D.Tup → ℝ := fun ξ' => D.R'.w ξ' * D.Gsel Θ P c ξ' π
    change 0 < (if ∑ ξ', f ξ' = 0 then (D.basePost Θ c.1 (D.obsOf π)).w ξ
      else f ξ / ∑ ξ', f ξ') at hq
    by_cases hsum : ∑ ξ', f ξ' = 0
    · have hqbase : 0 < (D.basePost Θ c.1 (D.obsOf π)).w ξ := by
        simpa [hsum] using hq
      exact hbase hqbase
    · have hsumNonneg : 0 ≤ ∑ ξ', f ξ' := by
        apply Finset.sum_nonneg
        intro ξ' hξ'
        exact mul_nonneg (D.R'.nonneg ξ') (D.Gsel_nonneg Θ P c ξ' π)
      have hsumPos : 0 < ∑ ξ', f ξ' := lt_of_le_of_ne hsumNonneg (Ne.symm hsum)
      have hqdiv : 0 < f ξ / ∑ ξ', f ξ' := by
        simpa [hsum] using hq
      have hprod : 0 < D.R'.w ξ * D.Gsel Θ P c ξ π := by
        by_contra hnot
        have hle : D.R'.w ξ * D.Gsel Θ P c ξ π ≤ 0 := le_of_not_gt hnot
        have hinv : 0 ≤ (∑ ξ', f ξ')⁻¹ := (inv_pos.mpr hsumPos).le
        have hmul : D.R'.w ξ * D.Gsel Θ P c ξ π * (∑ ξ', f ξ')⁻¹ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hle hinv
        have hpositive : 0 < D.R'.w ξ * D.Gsel Θ P c ξ π * (∑ ξ', f ξ')⁻¹ := by
          simpa [div_eq_mul_inv] using hqdiv
        exact (not_le_of_gt hpositive) hmul
      have hGpos : 0 < D.Gsel Θ P c ξ π := by
        have hR : 0 ≤ D.R'.w ξ := D.R'.nonneg ξ
        by_contra hnot
        have hG' : D.Gsel Θ P c ξ π ≤ 0 := le_of_not_gt hnot
        have hmul : D.R'.w ξ * D.Gsel Θ P c ξ π ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hR hG'
        exact (not_le_of_gt hprod) hmul
      exact lt_of_lt_of_le hGpos hG
  · exact hbase hq

end HypercubeRamsey.S08
