import HypercubeRamsey.S11.Core.SliceSigma_q_s11_slice

namespace HypercubeRamsey.Lane_q_s11_slice

open HypercubeRamsey
open HypercubeRamsey.S11.Core
open Filter
open scoped BigOperators

noncomputable section

def pairIndex_q_s11_slice {I : Type} [Fintype I] [DecidableEq I]
    (a c : I) : Option (Pair I) :=
  if hc : c = a then none else
    some ⟨{a, c}, Finset.card_pair (Ne.symm hc)⟩

theorem pairIndex_injective_q_s11_slice {I : Type} [Fintype I] [DecidableEq I]
    (a : I) : Function.Injective (pairIndex_q_s11_slice a) := by
  classical
  intro c d h
  by_cases hca : c = a
  · subst c
    by_cases hda : d = a
    · simpa [pairIndex_q_s11_slice, hda]
    · simp [pairIndex_q_s11_slice, hda] at h
  · by_cases hda : d = a
    · subst d
      simp [pairIndex_q_s11_slice, hca] at h
    · have hp :
          (⟨{a, c}, Finset.card_pair (Ne.symm hca)⟩ : Pair I) =
            ⟨{a, d}, Finset.card_pair (Ne.symm hda)⟩ := by
        exact Option.some.inj (by simpa [pairIndex_q_s11_slice, hca, hda] using h)
      have hs : ({a, c} : Finset I) = {a, d} := by
        exact congrArg Subtype.val hp
      have hc : c ∈ ({a, d} : Finset I) := by
        rw [← hs]
        simp
      have hc' : c = a ∨ c = d := by simpa using hc
      rcases hc' with hc' | hcd
      · exact (hca hc').elim
      · exact hcd

theorem ballStar_projection_q_s11_slice {N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    {k : ℕ} (W : Option (Pair I) → Fin k → Fin N) (a : I) :
    (fun c => W (pairIndex_q_s11_slice a c)) = ballStar W a := by
  classical
  funext c
  by_cases hc : c = a
  · subst c
    simp [pairIndex_q_s11_slice, ballStar]
  · simp [pairIndex_q_s11_slice, ballStar, hc]

noncomputable def rowTestFail_q_s11_slice {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}
    (g : ℝ) (μ ν : Law N) (ws : I → Fin k → Fin N) : ℝ := by
  classical
  exact if Passes E G g μ ν ws then 0 else 1

theorem row_fail_marginal_q_s11_slice {N : ℕ} (E : Fin N → Fin N → Prop)
    (G : Colour) {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}
    (g : ℝ) (μ ν : Law N) (y₀ : Fin N) (a : I) :
    (∑ W : Option (Pair I) → (Fin k → Fin N),
      ballW E G μ y₀ W *
        rowTestFail_q_s11_slice E G g μ ν (ballStar W a)) =
      testFail E G I k g μ ν y₀ := by
  classical
  let P : FinProb (Fin k → Fin N) := tupLaw E G μ y₀ k
  let f : (I → Fin k → Fin N) → ℝ := fun ws =>
    if Passes E G g μ ν ws then 0 else 1
  have hproj := pi_expect_injective_projection P (pairIndex_q_s11_slice a)
    (pairIndex_injective_q_s11_slice a) (fun _ : Fin k => y₀) f
  calc
    (∑ W : Option (Pair I) → (Fin k → Fin N),
        ballW E G μ y₀ W *
          (if Passes E G g μ ν (ballStar W a) then 0 else 1)) =
      (FinProb.pi (fun _ : Option (Pair I) => P)).expect
          (fun W => if Passes E G g μ ν (ballStar W a) then 0 else 1) := by
      simp [FinProb.expect, FinProb.pi, ballW, P, tupLaw, tupW, rowTestFail_q_s11_slice]
    _ = (FinProb.pi (fun _ : I => P)).expect f := by
      simpa [f, ballStar_projection_q_s11_slice] using hproj
    _ = testFail E G I k g μ ν y₀ := by
      simp [FinProb.expect, FinProb.pi, f, testFail, starW, P, tupLaw, tupW]

set_option maxHeartbeats 0 in
theorem sigma_fail_q_s11_slice :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
      (μ ν : Law N) (y₀ : Fin N),
      μ.WidthLE ((n : ℝ) ^ ((1 : ℝ) / 100)) →
      (∀ y, ν.w y ≠ 0 → 1 / 2 + 2 * gS n ≤ colDeg E G μ y) →
      ν.w y₀ ≠ 0 →
      sigmaFail E G (InnerCoord n) (kTup n) (gS n) μ ν y₀ ≤
        Real.exp (-(1 / 2 : ℝ) * gS n * kTup n * Fintype.card (InnerCoord n)) +
          (Fintype.card (InnerCoord n) : ℝ) *
            testFail E G (InnerCoord n) (kTup n) (gS n) μ ν y₀ := by
  obtain ⟨n₀, hparams⟩ := sigma_parameters_q_s11_slice
  refine ⟨n₀, ?_⟩
  intro n hn N E G μ ν y₀ hwidth hhigh hy₀
  classical
  rcases hparams n hn with ⟨hn1, hgs, hpow08, hpow01, hHlower, hmargin⟩
  let I := InnerCoord n
  let k := kTup n
  let T := Fin k → Fin N
  let U := Pair I → T
  let P : FinProb T := tupLaw E G μ y₀ k
  let qU : FinProb U := FinProb.pi (fun _ : Pair I => P)
  let passAll (W : Option (Pair I) → T) : Prop :=
    ∀ a : I, Passes E G (gS n) μ ν (ballStar W a)
  let rowFail (W : Option (Pair I) → T) : ℝ := if passAll W then 0 else 1
  let smallZ (z : I → Fin N) : Prop :=
    (commonSet E G μ z).card <
      (N : ℝ) * Real.exp (-((Real.log 2 - gS n / 2) * Fintype.card I))
  let smallPass (W : Option (Pair I) → T) (z : I → Fin N) : ℝ :=
    if passAll W ∧ smallZ z then 1 else 0
  let badSigma (W : Option (Pair I) → T) (z : I → Fin N) : ℝ :=
    if ∑ x, sigmaW E G (gS n) μ z x = 1 then 0 else 1
  let mkW (t : T) (v : U) : Option (Pair I) → T :=
    joinRadiusTwo_q_s11_slice t v
  let F (t : T) (v : U) (z : I → Fin N) : ℝ :=
    if ∀ a : I, Passes E G (gS n) μ ν (ballStar (mkW t v) a) then
      outW E G (gS n) μ ν (mkW t v) z else 0
  let m (v : U) (z : I → Fin N) : ℝ := ∑ t, P.w t * F t v z
  let H : ℝ := Fintype.card I
  let ε : ℝ := Real.exp (-(1 / 2 : ℝ) * gS n * k * H)
  let s : ℝ := H * ((Real.log 2 - 2 * gS n) * k)
  have hNnat : 0 < N := by have hy := y₀.isLt; omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNnat
  have hg : 0 < gS n := by unfold gS; positivity
  have hkPow : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 5) :=
    Real.one_le_rpow (by exact_mod_cast hn1) (by norm_num)
  have hkNat : 1 ≤ k := by
    have hceil : (n : ℝ) ^ ((1 : ℝ) / 5) ≤ (k : ℝ) := by
      dsimp [k, kTup]
      exact_mod_cast Nat.le_ceil ((n : ℝ) ^ ((1 : ℝ) / 5))
    exact_mod_cast le_trans hkPow hceil
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hHone : 1 ≤ (Fintype.card I : ℝ) := by
    have hleft : 1 ≤ (1 / 2 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 10) := by
      nlinarith [hpow01]
    exact hleft.trans (by simpa [I] using hHlower)
  have hHpos : 0 < H := by dsimp [H]; linarith [hHone]
  have hεpos : 0 < ε := by positivity
  have hballNonneg (W : Option (Pair I) → T) : 0 ≤ ballW E G μ y₀ W := by
    unfold ballW tupW
    apply Finset.prod_nonneg
    intro o ho
    apply Finset.prod_nonneg
    intro j hj
    exact (rhoLaw E G μ y₀).nonneg (W o j)
  let rowLaw (W : Option (Pair I) → T) (a : I) : FinProb (Fin N) := {
    w := fun y => oddRowW (E := E) (G := G) (I := I) (k := k)
      (gS n) μ ν (ballStar W a) y
    nonneg := fun y => oddRowW_nonneg_q_s11_slice E G (gS n) μ ν (ballStar W a) y
    sum_eq_one := oddRowW_sum_q_s11_slice E G (gS n) μ ν (ballStar W a) }
  have hOutSum (W : Option (Pair I) → T) :
      ∑ z : I → Fin N, outW E G (gS n) μ ν W z = 1 := by
    simpa [outW, rowLaw, FinProb.pi] using (FinProb.pi (rowLaw W)).sum_eq_one
  have hOutNonneg (W : Option (Pair I) → T) (z : I → Fin N) :
      0 ≤ outW E G (gS n) μ ν W z := by
    unfold outW
    apply Finset.prod_nonneg
    intro a ha
    exact (rowLaw W a).nonneg (z a)
  have hfailMarginal (a : I) :
      (∑ W : Option (Pair I) → T,
        ballW E G μ y₀ W *
          (if Passes E G (gS n) μ ν (ballStar W a) then 0 else 1)) =
        testFail E G I k (gS n) μ ν y₀ := by
    exact row_fail_marginal_q_s11_slice E G (gS n) μ ν y₀ a
  have hfailPoint (W : Option (Pair I) → T) :
      rowFail W ≤ ∑ a : I,
        (if Passes E G (gS n) μ ν (ballStar W a) then 0 else 1) := by
    by_cases hp : passAll W
    · simp only [rowFail, if_pos hp]
      exact Finset.sum_nonneg (fun a ha => by split_ifs <;> norm_num)
    · have hbad : ∃ a : I, ¬ Passes E G (gS n) μ ν (ballStar W a) := by
        simpa [passAll] using hp
      obtain ⟨a, ha⟩ := hbad
      have hsingle := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun b : I => if Passes E G (gS n) μ ν (ballStar W b) then (0 : ℝ) else 1)
        (fun b hb => by split_ifs <;> norm_num)
        (Finset.mem_univ a)
      simpa [rowFail, hp, ha] using hsingle
  have hfailExpected :
      (∑ W : Option (Pair I) → T, ballW E G μ y₀ W * rowFail W) ≤
        (Fintype.card I : ℝ) * testFail E G I k (gS n) μ ν y₀ := by
    calc
      (∑ W, ballW E G μ y₀ W * rowFail W) ≤
          ∑ W, ballW E G μ y₀ W *
            ∑ a : I, (if Passes E G (gS n) μ ν (ballStar W a) then 0 else 1) := by
        apply Finset.sum_le_sum
        intro W hW
        exact mul_le_mul_of_nonneg_left (hfailPoint W) (hballNonneg W)
      _ = ∑ a : I, ∑ W : Option (Pair I) → T,
            ballW E G μ y₀ W *
              (if Passes E G (gS n) μ ν (ballStar W a) then 0 else 1) := by
        calc
          (∑ W, ballW E G μ y₀ W *
              ∑ a : I, (if Passes E G (gS n) μ ν (ballStar W a) then 0 else 1)) =
            ∑ W, ∑ a : I, ballW E G μ y₀ W *
              (if Passes E G (gS n) μ ν (ballStar W a) then 0 else 1) := by
                apply Finset.sum_congr rfl
                intro W hW
                exact Finset.mul_sum Finset.univ
                  (fun a : I => if Passes E G (gS n) μ ν (ballStar W a) then (0 : ℝ) else 1)
                  (ballW E G μ y₀ W)
          _ = _ := Finset.sum_comm
      _ = (Fintype.card I : ℝ) * testFail E G I k (gS n) μ ν y₀ := by
        calc
          (∑ a : I, ∑ W : Option (Pair I) → T,
              ballW E G μ y₀ W *
                (if Passes E G (gS n) μ ν (ballStar W a) then 0 else 1)) =
              ∑ a : I, testFail E G I k (gS n) μ ν y₀ := by
            apply Finset.sum_congr rfl
            intro a ha
            exact hfailMarginal a
          _ = (Fintype.card I : ℝ) * testFail E G I k (gS n) μ ν y₀ := by
            simp [Finset.sum_const, nsmul_eq_mul]
  let delQ (v : U) : FinProb (I → Fin N) :=
    FinProb.pi (fun a : I => deletionLaw_q_s11_slice E G μ ν y₀ v a)
  have hFnonneg (t : T) (v : U) (z : I → Fin N) : 0 ≤ F t v z := by
    dsimp [F]
    split_ifs
    · exact hOutNonneg (mkW t v) z
    · exact le_rfl
  have hQdom (t : T) (v : U) (z : I → Fin N) :
      F t v z ≤ Real.exp s * (delQ v).w z := by
    by_cases hp : passAll (mkW t v)
    · have hpass : ∀ a : I, Passes E G (gS n) μ ν (ballStar (mkW t v) a) := by
        simpa [passAll] using hp
      have hrowBound (a : I) :
          oddRowW (E := E) (G := G) (I := I) (k := k) (gS n) μ ν
            (ballStar (mkW t v) a) (z a) ≤
          Real.exp ((Real.log 2 - 2 * gS n) * k) *
            (deletionLaw_q_s11_slice E G μ ν y₀ v a).w (z a) := by
        exact oddRow_le_deletion_q_s11_slice E G (gS n) μ ν y₀ hg hgs hhigh
          t v a (hpass a) (z a)
      have hprod :
          outW E G (gS n) μ ν (mkW t v) z ≤
            ∏ a : I, Real.exp ((Real.log 2 - 2 * gS n) * k) *
              (deletionLaw_q_s11_slice E G μ ν y₀ v a).w (z a) := by
        unfold outW
        apply Finset.prod_le_prod₀
        · intro a ha
          exact oddRowW_nonneg_q_s11_slice E G (gS n) μ ν
            (ballStar (mkW t v) a) (z a)
        · intro a ha
          exact hrowBound a
      have hcprod :
          (∏ a : I, Real.exp ((Real.log 2 - 2 * gS n) * k)) = Real.exp s := by
        calc
          (∏ a : I, Real.exp ((Real.log 2 - 2 * gS n) * k)) =
              Real.exp ((Real.log 2 - 2 * gS n) * k) ^ Fintype.card I := by simp
          _ = Real.exp ((Fintype.card I : ℝ) * ((Real.log 2 - 2 * gS n) * k)) :=
            (Real.exp_nat_mul ((Real.log 2 - 2 * gS n) * k) (Fintype.card I)).symm
          _ = Real.exp s := by
            apply congrArg Real.exp
            dsimp [s, H]
      calc
        F t v z = outW E G (gS n) μ ν (mkW t v) z := by
          dsimp [F]
          rw [if_pos hpass]
        _ ≤ ∏ a : I, Real.exp ((Real.log 2 - 2 * gS n) * k) *
            (deletionLaw_q_s11_slice E G μ ν y₀ v a).w (z a) := hprod
        _ = (∏ a : I, Real.exp ((Real.log 2 - 2 * gS n) * k)) *
            (∏ a : I, (deletionLaw_q_s11_slice E G μ ν y₀ v a).w (z a)) := by
              rw [Finset.prod_mul_distrib]
        _ = Real.exp s * (delQ v).w z := by
              rw [hcprod]
              rfl
    · have hnot : ¬ ∀ a : I, Passes E G (gS n) μ ν (ballStar (mkW t v) a) := by
        simpa [passAll] using hp
      have hFzero : F t v z = 0 := by
        dsimp [F]
        rw [if_neg hnot]
      rw [hFzero]
      exact mul_nonneg (Real.exp_nonneg _) ((delQ v).nonneg z)
  have hbadmass (v : U) :
      (∑ z : I → Fin N,
        if m v z < ε * (delQ v).w z ∨ m v z = 0 then m v z else 0) ≤ ε := by
    simpa [m] using (HypercubeRamsey.gated_posterior P (fun t z => F t v z)
      (fun t z => hFnonneg t v z) (delQ v) ε s hεpos).1
  have hTailFixed (v : U) :
      (∑ z : I → Fin N, m v z * (if smallZ z then 1 else 0)) ≤ ε := by
    have ht := fixed_pair_data_tail_q_s11_slice E G (gS n) μ ν y₀
      ((n : ℝ) ^ ((1 : ℝ) / 100)) hwidth hg hgs hhigh hy₀ hNreal hkreal hmargin v
    simpa [m, F, passAll, mkW, H, ε, smallZ, P, I, k,
      pairGateOutput_q_s11_slice, joinRadiusTwo_q_s11_slice] using ht
  let fW (W : Option (Pair I) → T) : ℝ :=
    ∑ z : I → Fin N, outW E G (gS n) μ ν W z * smallPass W z
  have hsmallFactor (t : T) (v : U) (z : I → Fin N) :
      outW E G (gS n) μ ν (mkW t v) z * smallPass (mkW t v) z =
        F t v z * (if smallZ z then 1 else 0) := by
    by_cases hp : passAll (mkW t v)
    · have hpass : ∀ a : I, Passes E G (gS n) μ ν (ballStar (mkW t v) a) := by
        simpa [passAll] using hp
      by_cases hs : smallZ z
      · simp [smallPass, passAll, F, mkW, hp, hpass, hs]
      · simp [smallPass, passAll, F, mkW, hp, hpass, hs]
    · have hnot : ¬ ∀ a : I, Passes E G (gS n) μ ν (ballStar (mkW t v) a) := by
        simpa [passAll] using hp
      by_cases hs : smallZ z
      · simp [smallPass, passAll, F, mkW, hp, hnot, hs]
      · simp [smallPass, passAll, F, mkW, hp, hnot, hs]
  have hinnerEq (v : U) :
      (∑ t : T, P.w t * fW (mkW t v)) =
        ∑ z : I → Fin N, m v z * (if smallZ z then 1 else 0) := by
    unfold fW m
    calc
      (∑ t : T, P.w t *
          ∑ z : I → Fin N, outW E G (gS n) μ ν (mkW t v) z * smallPass (mkW t v) z) =
        ∑ t : T, ∑ z : I → Fin N,
          P.w t * (outW E G (gS n) μ ν (mkW t v) z * smallPass (mkW t v) z) := by
            simp_rw [Finset.mul_sum]
      _ = ∑ z : I → Fin N, ∑ t : T,
          P.w t * (F t v z * (if smallZ z then 1 else 0)) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro t ht
            apply Finset.sum_congr rfl
            intro z hz
            rw [hsmallFactor]
      _ = ∑ z : I → Fin N, m v z * (if smallZ z then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro z hz
            calc
              (∑ t : T, P.w t * (F t v z * (if smallZ z then 1 else 0))) =
                  ∑ t : T, (P.w t * F t v z) * (if smallZ z then 1 else 0) := by
                apply Finset.sum_congr rfl
                intro t ht
                ring
              _ = (∑ t : T, P.w t * F t v z) * (if smallZ z then 1 else 0) := by
                rw [Finset.sum_mul]
              _ = m v z * (if smallZ z then 1 else 0) := rfl
  have hsmallExpected :
      (∑ W : Option (Pair I) → T, ballW E G μ y₀ W * fW W) ≤ ε := by
    have hsplit :
        (∑ W : Option (Pair I) → T, ballW E G μ y₀ W * fW W) =
          ∑ v : U, qU.w v * ∑ t : T, P.w t * fW (mkW t v) := by
      have hballWeight (W : Option (Pair I) → T) :
          ballW E G μ y₀ W = (FinProb.pi (fun _ : Option (Pair I) => P)).w W := by
        simp [FinProb.pi, ballW, P, tupLaw, tupW]
      calc
        (∑ W : Option (Pair I) → T, ballW E G μ y₀ W * fW W) =
            (FinProb.pi (fun _ : Option (Pair I) => P)).expect fW := by
              apply Finset.sum_congr rfl
              intro W hW
              rw [hballWeight]
        _ = (FinProb.bind P (fun _ => qU)).expect
            (fun p => fW (mkW p.1 p.2)) :=
              pi_expect_option_split P fW
        _ = ∑ v : U, qU.w v * ∑ t : T, P.w t * fW (mkW t v) := by
              change (∑ p : T × U, P.w p.1 * qU.w p.2 *
                fW (mkW p.1 p.2)) = _
              rw [Fintype.sum_prod_type, Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro v hv
              calc
                (∑ t : T, P.w t * qU.w v * fW (mkW t v)) =
                    ∑ t : T, qU.w v * (P.w t * fW (mkW t v)) := by
                  apply Finset.sum_congr rfl
                  intro t ht
                  ring
                _ = qU.w v * ∑ t : T, P.w t * fW (mkW t v) := by
                  rw [Finset.mul_sum]
    calc
      (∑ W : Option (Pair I) → T, ballW E G μ y₀ W * fW W) =
          ∑ v : U, qU.w v * ∑ t : T, P.w t * fW (mkW t v) := hsplit
      _ = ∑ v : U, qU.w v *
          ∑ z : I → Fin N, m v z * (if smallZ z then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [hinnerEq]
      _ ≤ ∑ v : U, qU.w v * ε := by
            apply Finset.sum_le_sum
            intro v hv
            exact mul_le_mul_of_nonneg_left (hTailFixed v) (qU.nonneg v)
      _ = ε := by
        calc
          (∑ v : U, qU.w v * ε) = (∑ v : U, qU.w v) * ε := by
            rw [← Finset.sum_mul]
          _ = ε := by rw [qU.sum_eq_one]; ring
  have hIndicator (W : Option (Pair I) → T) (z : I → Fin N) :
      badSigma W z ≤ rowFail W + smallPass W z := by
    by_cases hs : ∑ x, sigmaW E G (gS n) μ z x = 1
    · change (if ∑ x, sigmaW E G (gS n) μ z x = 1 then 0 else 1) ≤ _
      rw [if_pos hs]
      exact add_nonneg (by unfold rowFail; split_ifs <;> norm_num)
        (by unfold smallPass; split_ifs <;> norm_num)
    · by_cases hp : passAll W
      · have hcut : ¬ (N : ℝ) *
            Real.exp (-((Real.log 2 - gS n / 2) * Fintype.card I)) ≤
              ((commonSet E G μ z).card : ℝ) := by
          intro hc
          have hmass := sigmaW_sum_eq_one_of_cutoff_q_s11_slice E G
            (gS n) μ z hNreal hc
          exact hs hmass
        have hsmall : smallZ z := lt_of_not_ge hcut
        simp [badSigma, hs, rowFail, smallPass, hp, hsmall]
      · simp [badSigma, hs, rowFail, smallPass, hp]
  have hpointSum (W : Option (Pair I) → T) :
      (∑ z : I → Fin N, outW E G (gS n) μ ν W z * badSigma W z) ≤
        rowFail W + fW W := by
    have hconst :
        (∑ z : I → Fin N, outW E G (gS n) μ ν W z * rowFail W) =
          rowFail W * ∑ z : I → Fin N, outW E G (gS n) μ ν W z := by
      calc
        (∑ z, outW E G (gS n) μ ν W z * rowFail W) =
            ∑ z, rowFail W * outW E G (gS n) μ ν W z := by
              apply Finset.sum_congr rfl
              intro z hz
              ring
        _ = rowFail W * ∑ z, outW E G (gS n) μ ν W z := by
              rw [Finset.mul_sum]
    have hWsplit :
        (∑ z : I → Fin N, outW E G (gS n) μ ν W z *
          (rowFail W + smallPass W z)) =
            rowFail W * ∑ z : I → Fin N, outW E G (gS n) μ ν W z + fW W := by
      calc
        (∑ z, outW E G (gS n) μ ν W z * (rowFail W + smallPass W z)) =
            ∑ z, (outW E G (gS n) μ ν W z * rowFail W +
              outW E G (gS n) μ ν W z * smallPass W z) := by
                apply Finset.sum_congr rfl
                intro z hz
                ring
        _ = (∑ z, outW E G (gS n) μ ν W z * rowFail W) + fW W := by
              calc
                _ = (∑ z, outW E G (gS n) μ ν W z * rowFail W) +
                    (∑ z, outW E G (gS n) μ ν W z * smallPass W z) :=
                      Finset.sum_add_distrib
                _ = _ := by rfl
        _ = rowFail W * ∑ z, outW E G (gS n) μ ν W z + fW W := by rw [hconst]
    calc
      (∑ z : I → Fin N, outW E G (gS n) μ ν W z * badSigma W z) ≤
          ∑ z : I → Fin N, outW E G (gS n) μ ν W z *
            (rowFail W + smallPass W z) := by
              apply Finset.sum_le_sum
              intro z hz
              exact mul_le_mul_of_nonneg_left (hIndicator W z) (hOutNonneg W z)
      _ = rowFail W * ∑ z : I → Fin N, outW E G (gS n) μ ν W z + fW W := hWsplit
      _ = rowFail W + fW W := by rw [hOutSum W]; ring
  calc
    sigmaFail E G I k (gS n) μ ν y₀ =
        ∑ W : Option (Pair I) → T, ballW E G μ y₀ W *
          ∑ z : I → Fin N, outW E G (gS n) μ ν W z * badSigma W z := rfl
    _ ≤ ∑ W : Option (Pair I) → T, ballW E G μ y₀ W * (rowFail W + fW W) := by
          apply Finset.sum_le_sum
          intro W hW
          exact mul_le_mul_of_nonneg_left (hpointSum W) (hballNonneg W)
    _ = (∑ W : Option (Pair I) → T, ballW E G μ y₀ W * rowFail W) +
          (∑ W : Option (Pair I) → T, ballW E G μ y₀ W * fW W) := by
          calc
            _ = ∑ W, (ballW E G μ y₀ W * rowFail W +
                ballW E G μ y₀ W * fW W) := by
                  apply Finset.sum_congr rfl
                  intro W hW
                  ring
            _ = _ := by rw [Finset.sum_add_distrib]
    _ ≤ ε + (Fintype.card I : ℝ) * testFail E G I k (gS n) μ ν y₀ := by
          simpa [add_comm] using add_le_add hfailExpected hsmallExpected

end

end HypercubeRamsey.Lane_q_s11_slice
