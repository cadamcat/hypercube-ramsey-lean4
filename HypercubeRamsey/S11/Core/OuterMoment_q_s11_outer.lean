import HypercubeRamsey.S11.Core.Definitions
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.Tools.Ramsey

namespace HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer

open Filter

theorem signed_fv_weight_difference {N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {wX wY err : ℝ} (G : Colour)
    (hdisc : DiscOne E X Y wX wY err)
    (μ ν π : Law N) (hμX : μ.SupportedIn X) (hνY : ν.SupportedIn Y)
    (hπY : π.SupportedIn Y) (hN : 0 < (N : ℝ))
    (hμWidth : μ.WidthLE (wX - Real.log 11))
    (hνWidth : ν.WidthLE wY) (hπWidth : π.WidthLE wY)
    (g : Fin N → ℝ) (hg : ∀ x, |g x| ≤ 5) (herr : 0 ≤ err) :
    |∑ x, μ.w x * g x *
      ((∑ y, ν.w y * fv E G x y) - (∑ y, π.w y * fv E G x y))| ≤ 24 * err := by
  classical
  let cp : ℝ := ∑ x, μ.w x * (6 + g x)
  let cm : ℝ := ∑ x, μ.w x * (6 - g x)
  have hμg : |∑ x, μ.w x * g x| ≤ 5 := by
    calc
      |∑ x, μ.w x * g x| ≤ ∑ x, |μ.w x * g x| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, μ.w x * |g x| := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [abs_mul, abs_of_nonneg (μ.nonneg x)]
      _ ≤ ∑ x, μ.w x * 5 := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hg x) (μ.nonneg x)
      _ = 5 := by rw [← Finset.sum_mul, μ.sum_eq_one]; ring
  have hcpEq : cp = 6 + ∑ x, μ.w x * g x := by
    dsimp [cp]
    calc
      (∑ x, μ.w x * (6 + g x)) =
          ∑ x, (6 * μ.w x + μ.w x * g x) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = 6 * ∑ x, μ.w x + ∑ x, μ.w x * g x := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 6 + ∑ x, μ.w x * g x := by rw [μ.sum_eq_one]; ring
  have hcmEq : cm = 6 - ∑ x, μ.w x * g x := by
    dsimp [cm]
    calc
      (∑ x, μ.w x * (6 - g x)) =
          ∑ x, (6 * μ.w x - μ.w x * g x) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = 6 * ∑ x, μ.w x - ∑ x, μ.w x * g x := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 6 - ∑ x, μ.w x * g x := by rw [μ.sum_eq_one]; ring
  have hcpLower : 1 ≤ cp := by rw [hcpEq]; have := (abs_le.mp hμg).1; linarith
  have hcpUpper : cp ≤ 11 := by rw [hcpEq]; have := (abs_le.mp hμg).2; linarith
  have hcmLower : 1 ≤ cm := by rw [hcmEq]; have := (abs_le.mp hμg).2; linarith
  have hcmUpper : cm ≤ 11 := by rw [hcmEq]; have := (abs_le.mp hμg).1; linarith
  have hcpPos : 0 < cp := lt_of_lt_of_le (by norm_num) hcpLower
  have hcmPos : 0 < cm := lt_of_lt_of_le (by norm_num) hcmLower
  have hcpCm : cp + cm = 12 := by rw [hcpEq, hcmEq]; ring
  let μplus : Law N := {
    w := fun x => μ.w x * (6 + g x) / cp
    nonneg := fun x => div_nonneg (mul_nonneg (μ.nonneg x) (by
      have := (abs_le.mp (hg x)).1
      linarith)) hcpPos.le
    sum_eq_one := by
      calc
        (∑ x, μ.w x * (6 + g x) / cp) = cp / cp := by
          rw [Finset.sum_div]
        _ = 1 := div_self hcpPos.ne'
  }
  let μminus : Law N := {
    w := fun x => μ.w x * (6 - g x) / cm
    nonneg := fun x => div_nonneg (mul_nonneg (μ.nonneg x) (by
      have := (abs_le.mp (hg x)).2
      linarith)) hcmPos.le
    sum_eq_one := by
      calc
        (∑ x, μ.w x * (6 - g x) / cm) = cm / cm := by
          rw [Finset.sum_div]
        _ = 1 := div_self hcmPos.ne'
  }
  have hplusSupport : μplus.SupportedIn X := by
    intro x hx
    change μ.w x * (6 + g x) / cp = 0
    rw [hμX x hx]
    simp
  have hminusSupport : μminus.SupportedIn X := by
    intro x hx
    change μ.w x * (6 - g x) / cm = 0
    rw [hμX x hx]
    simp
  have hplusWidth : μplus.WidthLE wX := by
    intro x
    change μ.w x * (6 + g x) / cp ≤ Real.exp wX / N
    have hratio : (6 + g x) / cp ≤ 11 := by
      apply (div_le_iff₀ hcpPos).2
      have h := (abs_le.mp (hg x)).2
      nlinarith
    calc
      μ.w x * (6 + g x) / cp = μ.w x * ((6 + g x) / cp) := by ring
      _ ≤ μ.w x * 11 := mul_le_mul_of_nonneg_left hratio (μ.nonneg x)
      _ ≤ (Real.exp (wX - Real.log 11) / N) * 11 :=
        mul_le_mul_of_nonneg_right (hμWidth x) (by norm_num)
      _ = Real.exp wX / N := by
        rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 11)]
        field_simp [ne_of_gt hN]
        <;> ring
  have hminusWidth : μminus.WidthLE wX := by
    intro x
    change μ.w x * (6 - g x) / cm ≤ Real.exp wX / N
    have hratio : (6 - g x) / cm ≤ 11 := by
      apply (div_le_iff₀ hcmPos).2
      have h := (abs_le.mp (hg x)).1
      nlinarith
    calc
      μ.w x * (6 - g x) / cm = μ.w x * ((6 - g x) / cm) := by ring
      _ ≤ μ.w x * 11 := mul_le_mul_of_nonneg_left hratio (μ.nonneg x)
      _ ≤ (Real.exp (wX - Real.log 11) / N) * 11 :=
        mul_le_mul_of_nonneg_right (hμWidth x) (by norm_num)
      _ = Real.exp wX / N := by
        rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 11)]
        field_simp [ne_of_gt hN]
        <;> ring
  have hdenRow (μ' ν' : Law N) :
      dens E G μ' ν' = ∑ x, μ'.w x * ∑ y, ν'.w y * hit E G x y := by
    simp only [dens]
    simp only [hit]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hfvRow (ν' : Law N) (x : Fin N) :
      (∑ y, ν'.w y * fv E G x y) =
        2 * (∑ y, ν'.w y * hit E G x y) - 1 := by
    unfold fv
    calc
      (∑ y, ν'.w y * (2 * hit E G x y - 1)) =
          ∑ y, (2 * (ν'.w y * hit E G x y) - ν'.w y) := by
            apply Finset.sum_congr rfl
            intro y hy
            ring
      _ = 2 * (∑ y, ν'.w y * hit E G x y) - ∑ y, ν'.w y := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * (∑ y, ν'.w y * hit E G x y) - 1 := by rw [ν'.sum_eq_one]
  have hfvDensity (μ' ν' π' : Law N) :
      (∑ x, μ'.w x *
        ((∑ y, ν'.w y * fv E G x y) - (∑ y, π'.w y * fv E G x y))) =
        2 * (dens E G μ' ν' - dens E G μ' π') := by
    calc
      _ = ∑ x, μ'.w x *
          (2 * ((∑ y, ν'.w y * hit E G x y) - (∑ y, π'.w y * hit E G x y))) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hfvRow ν' x, hfvRow π' x]
            ring
      _ = 2 * ((∑ x, μ'.w x * ∑ y, ν'.w y * hit E G x y) -
          (∑ x, μ'.w x * ∑ y, π'.w y * hit E G x y)) := by
            calc
              (∑ x, μ'.w x *
                  (2 * ((∑ y, ν'.w y * hit E G x y) - (∑ y, π'.w y * hit E G x y)))) =
                  ∑ x, 2 * (μ'.w x *
                    ((∑ y, ν'.w y * hit E G x y) - (∑ y, π'.w y * hit E G x y))) := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      ring
              _ = 2 * ∑ x, μ'.w x *
                    ((∑ y, ν'.w y * hit E G x y) - (∑ y, π'.w y * hit E G x y)) := by
                      rw [Finset.mul_sum]
              _ = 2 * ((∑ x, μ'.w x * ∑ y, ν'.w y * hit E G x y) -
                    (∑ x, μ'.w x * ∑ y, π'.w y * hit E G x y)) := by
                      congr 1
                      calc
                        (∑ x, μ'.w x *
                            ((∑ y, ν'.w y * hit E G x y) - (∑ y, π'.w y * hit E G x y))) =
                            ∑ x, (μ'.w x * (∑ y, ν'.w y * hit E G x y) -
                              μ'.w x * (∑ y, π'.w y * hit E G x y)) := by
                                apply Finset.sum_congr rfl
                                intro x hx
                                ring
                        _ =
                            (∑ x, μ'.w x * ∑ y, ν'.w y * hit E G x y) -
                              (∑ x, μ'.w x * ∑ y, π'.w y * hit E G x y) := by
                                rw [Finset.sum_sub_distrib]
      _ = 2 * (dens E G μ' ν' - dens E G μ' π') := by
            rw [← hdenRow, ← hdenRow]
  have hdiscPlusNu := hdisc μplus ν hplusSupport hνY hplusWidth hνWidth G
  have hdiscPlusPi := hdisc μplus π hplusSupport hπY hplusWidth hπWidth G
  have hdiscMinusNu := hdisc μminus ν hminusSupport hνY hminusWidth hνWidth G
  have hdiscMinusPi := hdisc μminus π hminusSupport hπY hminusWidth hπWidth G
  have hplusDelta :
      |∑ x, μplus.w x *
        ((∑ y, ν.w y * fv E G x y) - (∑ y, π.w y * fv E G x y))| ≤ 4 * err := by
    rw [hfvDensity]
    have hdiff : |dens E G μplus ν - dens E G μplus π| ≤ 2 * err := by
      calc
        |dens E G μplus ν - dens E G μplus π| ≤
            |dens E G μplus ν - 1 / 2| + |dens E G μplus π - 1 / 2| := by
              calc
                _ = |(dens E G μplus ν - 1 / 2) -
                      (dens E G μplus π - 1 / 2)| := by congr 1 <;> ring
                _ ≤ _ := abs_sub _ _
        _ ≤ err + err := add_le_add hdiscPlusNu hdiscPlusPi
        _ = 2 * err := by ring
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hminusDelta :
      |∑ x, μminus.w x *
        ((∑ y, ν.w y * fv E G x y) - (∑ y, π.w y * fv E G x y))| ≤ 4 * err := by
    rw [hfvDensity]
    have hdiff : |dens E G μminus ν - dens E G μminus π| ≤ 2 * err := by
      calc
        |dens E G μminus ν - dens E G μminus π| ≤
            |dens E G μminus ν - 1 / 2| + |dens E G μminus π - 1 / 2| := by
              calc
                _ = |(dens E G μminus ν - 1 / 2) -
                      (dens E G μminus π - 1 / 2)| := by congr 1 <;> ring
                _ ≤ _ := abs_sub _ _
        _ ≤ err + err := add_le_add hdiscMinusNu hdiscMinusPi
        _ = 2 * err := by ring
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  let F : Fin N → ℝ := fun x =>
    (∑ y, ν.w y * fv E G x y) - (∑ y, π.w y * fv E G x y)
  have hweightPlus (x : Fin N) : cp * μplus.w x = μ.w x * (6 + g x) := by
    change cp * (μ.w x * (6 + g x) / cp) = _
    field_simp [ne_of_gt hcpPos]
  have hweightMinus (x : Fin N) : cm * μminus.w x = μ.w x * (6 - g x) := by
    change cm * (μ.w x * (6 - g x) / cm) = _
    field_simp [ne_of_gt hcmPos]
  have hpoint (x : Fin N) :
      μ.w x * (6 + g x) - μ.w x * (6 - g x) =
        cp * μplus.w x - cm * μminus.w x := by
    rw [hweightPlus, hweightMinus]
  have hsumPlus : (∑ x, cp * μplus.w x * F x) =
      cp * (∑ x, μplus.w x * F x) := by
    calc
      (∑ x, cp * μplus.w x * F x) =
          ∑ x, cp * (μplus.w x * F x) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = cp * (∑ x, μplus.w x * F x) := by rw [Finset.mul_sum]
  have hsumMinus : (∑ x, cm * μminus.w x * F x) =
      cm * (∑ x, μminus.w x * F x) := by
    calc
      (∑ x, cm * μminus.w x * F x) =
          ∑ x, cm * (μminus.w x * F x) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = cm * (∑ x, μminus.w x * F x) := by rw [Finset.mul_sum]
  have hidentity : 2 * (∑ x, μ.w x * g x * F x) =
      cp * (∑ x, μplus.w x * F x) - cm * (∑ x, μminus.w x * F x) := by
    calc
      2 * (∑ x, μ.w x * g x * F x) =
          ∑ x, 2 * (μ.w x * g x * F x) := by rw [Finset.mul_sum]
      _ = ∑ x, (μ.w x * (6 + g x) - μ.w x * (6 - g x)) * F x := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = ∑ x, (cp * μplus.w x - cm * μminus.w x) * F x := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hpoint x]
      _ = cp * (∑ x, μplus.w x * F x) - cm * (∑ x, μminus.w x * F x) := by
            calc
              (∑ x, (cp * μplus.w x - cm * μminus.w x) * F x) =
                  (∑ x, cp * μplus.w x * F x) -
                    (∑ x, cm * μminus.w x * F x) := by
                      calc
                        _ = ∑ x, (cp * μplus.w x * F x - cm * μminus.w x * F x) := by
                              apply Finset.sum_congr rfl
                              intro x hx
                              ring
                        _ = _ := by rw [Finset.sum_sub_distrib]
              _ = cp * (∑ x, μplus.w x * F x) - cm * (∑ x, μminus.w x * F x) := by
                    rw [hsumPlus, hsumMinus]
  exact calc
    |∑ x, μ.w x * g x * F x| =
        |(cp * (∑ x, μplus.w x * F x) - cm * (∑ x, μminus.w x * F x)) / 2| := by
          congr 1
          linarith [hidentity]
    _ = |cp * (∑ x, μplus.w x * F x) - cm * (∑ x, μminus.w x * F x)| / 2 := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (cp * (4 * err) + cm * (4 * err)) / 2 :=
          by
            have hnum :
                |cp * (∑ x, μplus.w x * F x) - cm * (∑ x, μminus.w x * F x)| ≤
                  cp * (4 * err) + cm * (4 * err) := by
              calc
                _ ≤ |cp * (∑ x, μplus.w x * F x)| +
                    |cm * (∑ x, μminus.w x * F x)| := abs_sub _ _
                _ = cp * |∑ x, μplus.w x * F x| +
                    cm * |∑ x, μminus.w x * F x| := by
                      rw [abs_mul, abs_mul, abs_of_nonneg hcpPos.le, abs_of_nonneg hcmPos.le]
                _ ≤ cp * (4 * err) + cm * (4 * err) := by
                      exact add_le_add (mul_le_mul_of_nonneg_left hplusDelta hcpPos.le)
                        (mul_le_mul_of_nonneg_left hminusDelta hcmPos.le)
            exact div_le_div_of_nonneg_right hnum (by norm_num)
    _ = 24 * err := by
          rw [← add_mul, hcpCm]
          ring

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

/-! ### Product-law conditioning

These finite reindexing lemmas let the one- and two-free estimates be integrated over the remaining coordinates of
an independent tuple. -/

private abbrev pairRest (u : ℕ) (j j' : Fin u) : Type :=
  {i : Fin u // i ∈ ((Finset.univ : Finset (Fin u)).erase j).erase j'}

private def pairTuple {u N : ℕ} (j j' : Fin u) (hjj : j ≠ j')
    (q : (Fin N × Fin N) × (pairRest u j j' → Fin N)) : Fin u → Fin N :=
  fun i => if h : i = j then q.1.1 else if h' : i = j' then q.1.2 else
    q.2 ⟨i, Finset.mem_erase.mpr ⟨h',
      Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩⟩⟩

private def pairBase {u N : ℕ} (j j' : Fin u) (hjj : j ≠ j')
    (x₀ : Fin N) (r : pairRest u j j' → Fin N) : Fin u → Fin N :=
  fun i => if h : i = j then x₀ else if h' : i = j' then x₀ else
    r ⟨i, Finset.mem_erase.mpr ⟨h',
      Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩⟩⟩

private def pairTupleEquiv {u N : ℕ} (j j' : Fin u) (hjj : j ≠ j') :
    (Fin N × Fin N) × (pairRest u j j' → Fin N) ≃ (Fin u → Fin N) where
  toFun := pairTuple j j' hjj
  invFun f := ((f j, f j'), fun i => f i.1)
  left_inv q := by
    rcases q with ⟨⟨x, z⟩, r⟩
    apply Prod.ext
    · apply Prod.ext
      · simp [pairTuple]
      · have hj' : j' ≠ j := Ne.symm hjj
        simp [pairTuple, hj']
    · funext i
      have h₁ : i.1 ≠ j' := (Finset.mem_erase.mp i.2).1
      have h₂ : i.1 ≠ j := (Finset.mem_erase.mp ((Finset.mem_erase.mp i.2).2)).1
      simp only [pairTuple, h₂, h₁]
      congr 1
  right_inv f := by
    funext i
    by_cases h : i = j
    · subst i
      simp [pairTuple]
    · by_cases h' : i = j'
      · subst i
        simp [pairTuple, h, hjj]
      · simp [pairTuple, h, h']

private def pairRestWeight {u N : ℕ} (σ : Fin N → ℝ) (j j' : Fin u)
    (r : pairRest u j j' → Fin N) : ℝ := ∏ i, σ (r i)

private theorem tupWt_pairTuple {u N : ℕ} (σ : Fin N → ℝ) (j j' : Fin u) (hjj : j ≠ j')
    (q : (Fin N × Fin N) × (pairRest u j j' → Fin N)) :
    tupWt σ (pairTuple j j' hjj q) = σ q.1.1 * σ q.1.2 * pairRestWeight σ j j' q.2 := by
  classical
  letI : Fintype (pairRest u j j') := inferInstance
  let f : Fin u → Fin N := pairTuple j j' hjj q
  have hj : j ∈ (Finset.univ : Finset (Fin u)) := Finset.mem_univ _
  have hj' : j' ∈ (Finset.univ : Finset (Fin u)).erase j := Finset.mem_erase.mpr ⟨hjj.symm, Finset.mem_univ _⟩
  have hrest : (∏ i : pairRest u j j', σ (f i.1)) =
      ∏ i ∈ ((Finset.univ : Finset (Fin u)).erase j).erase j', σ (f i) := by
    simpa [pairRest] using
      (Finset.prod_coe_sort (((Finset.univ : Finset (Fin u)).erase j).erase j')
        (fun i : Fin u => σ (f i)))
  have hprod : (∏ i : Fin u, σ (f i)) =
      σ (f j) * σ (f j') * (∏ i : pairRest u j j', σ (f i.1)) := by
    rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin u)) (fun i => σ (f i)) hj]
    rw [← Finset.prod_erase_mul ((Finset.univ : Finset (Fin u)).erase j)
      (fun i => σ (f i)) hj']
    rw [← hrest]
    ring
  have hprodRest : (∏ i : pairRest u j j', σ (f i.1)) =
      ∏ i : pairRest u j j', σ (q.2 i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have h₁ : i.1 ≠ j' := (Finset.mem_erase.mp i.2).1
    have h₂ : i.1 ≠ j := (Finset.mem_erase.mp ((Finset.mem_erase.mp i.2).2)).1
    simp [f, pairTuple, h₁, h₂]
  unfold tupWt
  rw [hprod]
  rw [hprodRest]
  simp [f, pairTuple, pairRestWeight, hjj.symm]

theorem tuple_event_mass_le_of_two_free {u N : ℕ} (σ : Fin N → ℝ) (S : Finset (Fin N))
    (hσ : ∀ x, 0 ≤ σ x) (hσsum : ∑ x, σ x = 1)
    (hσsupp : ∀ x, σ x ≠ 0 → x ∈ S) (j j' : Fin u) (hjj : j ≠ j')
    (x₀ : Fin N) (hx₀ : x₀ ∈ S) (P : (Fin u → Fin N) → Prop) [DecidablePred P]
    (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ∀ base : Fin u → Fin N, (∀ i, base i ∈ S) →
      (∑ x, ∑ z, σ x * σ z *
        (if P (Function.update (Function.update base j x) j' z) then 1 else 0)) ≤ ε) :
    (∑ f : Fin u → Fin N, tupWt σ f * (if P f then 1 else 0)) ≤ ε := by
  classical
  let R := pairRest u j j'
  letI : Fintype R := inferInstance
  let e := pairTupleEquiv (u := u) (N := N) j j' hjj
  let rw (r : R → Fin N) : ℝ := pairRestWeight σ j j' r
  have hsumRest : (∑ r : R → Fin N, rw r) = 1 := by
    dsimp [rw, pairRestWeight]
    calc
      (∑ r : R → Fin N, ∏ i, σ (r i)) = ∏ i : R, ∑ x, σ x := by
        symm
        exact Fintype.prod_sum (fun (_ : R) (x : Fin N) => σ x)
      _ = 1 := by simp [hσsum]
  have hrest_nonneg (r : R → Fin N) : 0 ≤ rw r := by
    dsimp [rw, pairRestWeight]
    exact Finset.prod_nonneg fun i hi => hσ (r i)
  have hrest_support (r : R → Fin N) (hr : rw r ≠ 0) (i : R) : r i ∈ S := by
    have hprod := hr
    change (∏ k : R, σ (r k)) ≠ 0 at hprod
    have hfactor := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
    exact hσsupp (r i) hfactor
  have hbase (r : R → Fin N) (hr : rw r ≠ 0) :
      ∀ i, pairBase j j' hjj x₀ r i ∈ S := by
    intro i
    by_cases h : i = j
    · simp [pairBase, h, hx₀]
    · by_cases h' : i = j'
      · simp [pairBase, h, h', hx₀]
      · have hrmem := hrest_support r hr ⟨i, Finset.mem_erase.mpr ⟨h',
          Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩⟩⟩
        simpa [pairBase, h, h'] using hrmem
  have hReindex :
      (∑ f : Fin u → Fin N, tupWt σ f * (if P f then 1 else 0)) =
        ∑ q : (Fin N × Fin N) × (R → Fin N),
          tupWt σ (e q) * (if P (e q) then 1 else 0) := by
    symm
    exact Fintype.sum_equiv e
      (fun q => tupWt σ (e q) * (if P (e q) then 1 else 0))
      (fun f => tupWt σ f * (if P f then 1 else 0)) (by intro q; rfl)
  rw [hReindex]
  have hfactor :
      (∑ q : (Fin N × Fin N) × (R → Fin N),
        tupWt σ (e q) * (if P (e q) then 1 else 0)) =
        ∑ r : R → Fin N, rw r *
          (∑ x, ∑ z, σ x * σ z * (if P (e ((x, z), r)) then 1 else 0)) := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Fintype.sum_prod_type]
    have hweight (x z : Fin N) : tupWt σ (e ((x, z), r)) = σ x * σ z * rw r := by
      change tupWt σ (pairTuple j j' hjj ((x, z), r)) = _
      rw [tupWt_pairTuple]
    simp_rw [hweight]
    calc
      (∑ x, ∑ z, σ x * σ z * rw r * (if P (e ((x, z), r)) then 1 else 0)) =
          rw r * (∑ x, ∑ z, σ x * σ z * (if P (e ((x, z), r)) then 1 else 0)) := by
        calc
          (∑ x, ∑ z, σ x * σ z * rw r * (if P (e ((x, z), r)) then 1 else 0)) =
              ∑ x, rw r * ∑ z, σ x * σ z * (if P (e ((x, z), r)) then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            calc
              (∑ z, σ x * σ z * rw r * (if P (e ((x, z), r)) then 1 else 0)) =
                  ∑ z, rw r * (σ x * σ z * (if P (e ((x, z), r)) then 1 else 0)) := by
                apply Finset.sum_congr rfl
                intro z hz
                ring
              _ = rw r * (∑ z, σ x * σ z * (if P (e ((x, z), r)) then 1 else 0)) := by
                rw [← Finset.mul_sum]
          _ = rw r * (∑ x, ∑ z, σ x * σ z * (if P (e ((x, z), r)) then 1 else 0)) := by
            rw [← Finset.mul_sum]
      _ = _ := rfl
  rw [hfactor]
  calc
    (∑ r : R → Fin N, rw r *
      (∑ x, ∑ z, σ x * σ z * (if P (e ((x, z), r)) then 1 else 0))) ≤
      ∑ r : R → Fin N, rw r * ε := by
        apply Finset.sum_le_sum
        intro r hr
        by_cases hr0 : rw r = 0
        · simp [hr0]
        · have hsupp := hbase r hr0
          have hUpdate : ∀ x z,
              e ((x, z), r) = Function.update (Function.update (pairBase j j' hjj x₀ r) j x) j' z := by
              intro x z
              funext i
              by_cases h : i = j
              · subst i
                simp [e, pairTupleEquiv, pairTuple, pairBase, Function.update, hjj, hjj.symm]
              · by_cases h' : i = j'
                · subst i
                  simp [e, pairTupleEquiv, pairTuple, pairBase, h, hjj.symm, Function.update]
                · simp [e, pairTupleEquiv, pairTuple, pairBase, h, h', Function.update]
          have hsmall := hbound (pairBase j j' hjj x₀ r) hsupp
          have hsmall' :
              (∑ x, ∑ z, σ x * σ z *
                (if P (e ((x, z), r)) then 1 else 0)) ≤ ε := by
            simpa [hUpdate] using hsmall
          exact mul_le_mul_of_nonneg_left hsmall' (hrest_nonneg r)
    _ = ε := by
      rw [← Finset.sum_mul, hsumRest]
      ring

theorem tuple_event_mass_le_of_one_free {u N : ℕ} (σ : Fin N → ℝ) (S : Finset (Fin N))
    (hσ : ∀ x, 0 ≤ σ x) (hσsum : ∑ x, σ x = 1)
    (hσsupp : ∀ x, σ x ≠ 0 → x ∈ S) (j j' : Fin u) (hjj : j ≠ j')
    (x₀ : Fin N) (hx₀ : x₀ ∈ S) (P : (Fin u → Fin N) → Prop) [DecidablePred P]
    (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ∀ base : Fin u → Fin N, (∀ i, base i ∈ S) →
      (∑ x, σ x * (if P (Function.update base j x) then 1 else 0)) ≤ ε) :
    (∑ f : Fin u → Fin N, tupWt σ f * (if P f then 1 else 0)) ≤ ε := by
  classical
  apply tuple_event_mass_le_of_two_free σ S hσ hσsum hσsupp j j' hjj x₀ hx₀ P ε hε
  intro base hbase
  have hcomm (x z : Fin N) :
      Function.update (Function.update base j x) j' z =
        Function.update (Function.update base j' z) j x :=
    Function.update_comm hjj x z base
  calc
    (∑ x, ∑ z, σ x * σ z *
      (if P (Function.update (Function.update base j x) j' z) then 1 else 0)) =
      ∑ z, σ z * ∑ x, σ x *
        (if P (Function.update (Function.update base j' z) j x) then 1 else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro z hz
          calc
            (∑ x, σ x * σ z *
              (if P (Function.update (Function.update base j x) j' z) then 1 else 0)) =
                ∑ x, σ z * (σ x *
                  (if P (Function.update (Function.update base j' z) j x) then 1 else 0)) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    rw [hcomm]
                    ring
            _ = σ z * (∑ x, σ x *
                (if P (Function.update (Function.update base j' z) j x) then 1 else 0)) := by
                  rw [Finset.mul_sum]
    _ ≤ ∑ z, σ z * ε := by
          apply Finset.sum_le_sum
          intro z hz
          by_cases hz0 : σ z = 0
          · simp [hz0]
          · have hzS : z ∈ S := hσsupp z hz0
            apply mul_le_mul_of_nonneg_left _ (hσ z)
            apply hbound (Function.update base j' z)
            intro i
            by_cases hi : i = j'
            · subst i
              simpa using hzS
            · simpa [hi] using hbase i
    _ = ε := by
          rw [← Finset.sum_mul, hσsum]
          ring

theorem sub_le_neg_of_add_le {x y z : ℝ} (h : x + y ≤ z) : x - z ≤ -y := by
  linarith

end HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer
