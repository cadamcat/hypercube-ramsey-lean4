import HypercubeRamsey.S06.Defs
import HypercubeRamsey.S05.Assembly
import HypercubeRamsey.S05.Stages_p_s05_h

/-!
# Section 6 preliminary reduction

L6.1a (06:28–65).  Either the opposite colour already has a cube (Lemma 5.1 applied to the laws `B_y` in
colour `!G`), or the symmetric parent relation `y ≍ y'` has a broad core `S₀`.  The parent record fixes the
heavy support, `Π'`, the relation and the partner laws used by all later Section 6 nodes.

Repair note.  The frozen `L6_1a` took `n₀ C₀` as universally quantified inputs; it was refuted with
`n₀ = 0, C₀ = 1/4, n = 2, N = 1`.  Lemma 5.1 and the heavy-support bounds need
`n` and `N/2^n` large, so the constants are now existential, before `∀ n N` (06:24–26).
-/

namespace HypercubeRamsey
namespace S06

open Classical
open OAI.HypercubeRamsey
open scoped BigOperators

noncomputable section

/-- The heavy support `{y : NΠ(y) ≥ n^{-D_*}}` (06:39). -/
def heavySet6 {n N : ℕ} (Dstar : ℝ) (π : Law N) : Finset (Fin N) :=
  Finset.univ.filter fun y => (n : ℝ) ^ (-Dstar) ≤ (N : ℝ) * π.w y

/-- The parent relation `y ≍ y'` (06:55–58); symmetric by definition. -/
def related6 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N) (y y' : Fin N) : Prop :=
  c₀ ≤ colDeg E G (broadLaw6 M y) y' ∧ c₀ ≤ colDeg E G (broadLaw6 M y') y

/-- Case 2 data of the reduction (06:53–65).  `Π'` is the normalized restriction of `Π` to the heavy set;
`S₀` are the labels with partner mass `≥ .1`. -/
structure ParentCase6 (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N) (γ Dstar : ℝ) where
  heavy : Finset (Fin N)
  heavy_eq : heavy = heavySet6 (n := n) Dstar (secondMixture6 M)
  piPrime : Law N
  retained_mass : 1 - (n : ℝ) ^ (-Dstar) ≤ ∑ y ∈ heavy, (secondMixture6 M).w y
  piPrime_eq : ∀ y, piPrime.w y =
    if y ∈ heavy then (secondMixture6 M).w y / ∑ y' ∈ heavy, (secondMixture6 M).w y' else 0
  piPrime_cap : ∀ y, piPrime.w y ≤ 2 * (secondMixture6 M).w y
  eta_cap : ∀ y ∈ heavy, ∀ i, (tagPosterior6 M y).w i ≤ (n : ℝ) ^ (2 * Dstar) * M.Λ i
  eta_mean : ∀ i, ∑ y, (secondMixture6 M).w y * (tagPosterior6 M y).w i = M.Λ i
  broad_width : ∀ y ∈ heavy, (broadLaw6 M y).WidthLE ((n : ℝ) ^ γ)
  S₀ : Finset (Fin N)
  S₀_eq : S₀ = heavy.filter fun y => (1 / 10 : ℝ) ≤ FinProb.pr piPrime (fun y' => related6 E G M y y')
  S₀_mass : (7 / 10 : ℝ) ≤ FinProb.pr piPrime (fun y => y ∈ S₀)
  partner_mass : ∀ y ∈ S₀, (1 / 10 : ℝ) ≤ FinProb.pr piPrime (fun y' => related6 E G M y y')
  partner_cap : ∀ y ∈ S₀, ∀ f z, (partnerLaw6 piPrime (related6 E G M) y f).w z ≤
    20 * (secondMixture6 M).w z

set_option maxHeartbeats 1000000 in
/-- L6.1a (06:28–65): for `n` and `N/2^n` large, either some colour has a cube (Case 1 via Lemma 5.1 in colour
`!G`, with tags `y ∈ S₁`, laws `B_y`, balance `40K`, and `χ = 1/(40K)` good columns of degree `> .99`), or
the Case 2 parent record exists.  The degree hypothesis of Lemma 6.1 is not needed here. -/
theorem L6_1a (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ∃ (n₀ : ℕ) (C₀ : ℝ), 0 < C₀ ∧ ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N),
      LargeAt n₀ C₀ n N → M.Balanced K →
      (∀ i, 0 < M.Λ i → (M.μ i).WidthLE ((n : ℝ) ^ γ)) →
      (∀ i, 0 < M.Λ i → (M.ν i).CapLE ((n : ℝ) ^ Dstar₆)) →
      CubeAt n N E ∨ Nonempty (ParentCase6 n N E G M γ Dstar₆) := by
  classical
  have hKpos : 0 < K := hadm.2.2.2
  have hK40 : 0 < 40 * K := by positivity
  have hChi : 0 < 1 / (40 * K) := by positivity
  obtain ⟨n₅, C₅, hL5⟩ := L5_1_consumed γ (40 * K) (1 / (40 * K))
    hadm.1 hadm.2.1 hK40 hChi
  have hDpos : 0 < Dstar₆ := constants6_facts.1
  have htendD : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ Dstar₆) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hDpos).comp tendsto_natCast_atTop_atTop
  obtain ⟨nD, hEventD⟩ := Filter.eventually_atTop.1
    (htendD.eventually (Filter.eventually_ge_atTop 2))
  let n₀ := max n₅ (max 400000 nD)
  let C₀ := max C₅ 1
  refine ⟨n₀, C₀, by dsimp [C₀]; positivity, ?_⟩
  intro n N E G M hLarge hBal hWidth hCap
  obtain ⟨hn₀, hNlow, hNup⟩ := hLarge
  have hn5 : n₅ ≤ n := le_trans (le_max_left _ _) hn₀
  have hn400000 : 400000 ≤ n := by
    have h := le_trans (le_max_right _ _) hn₀
    omega
  have hnD : nD ≤ n := by
    have h := le_trans (le_max_right _ _) hn₀
    omega
  have hC01 : 1 ≤ C₀ := by dsimp [C₀]; exact le_max_right _ _
  have hC5 : C₅ ≤ C₀ := by dsimp [C₀]; exact le_max_left _ _
  have hC0pos : 0 < C₀ := by dsimp [C₀]; positivity
  have hLarge5 : LargeAt n₅ C₅ n N := by
    refine ⟨hn5, ?_, hNup⟩
    calc
      C₅ * (2 : ℝ) ^ n ≤ C₀ * (2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hC5 (by positivity)
      _ ≤ (N : ℝ) := hNlow
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnRpos : 0 < (n : ℝ) := by positivity
  have hNpos : 0 < (N : ℝ) := by
    have hprod : 0 < C₀ * (2 : ℝ) ^ n := mul_pos hC0pos (by positivity)
    exact lt_of_lt_of_le hprod hNlow
  have hNposNat : 0 < N := by exact_mod_cast hNpos
  have hDpow : 2 ≤ (n : ℝ) ^ Dstar₆ := hEventD n hnD
  have hDsmall : (n : ℝ) ^ (-Dstar₆) ≤ 1 / 2 := by
    rw [Real.rpow_neg hnRpos.le]
    simpa [one_div] using one_div_le_one_div_of_le (by norm_num) hDpow
  let Pi : Law N := secondMixture6 M
  have hPiCap : ∀ y, (N : ℝ) * Pi.w y ≤ K := by
    intro y
    simpa [Pi, secondMixture6, Law.mix, tagLaw6] using hBal.2 y
  have hPostNum (y : Fin N) (i : M.ι) :
      Pi.w y * (tagPosterior6 M y).w i = M.Λ i * (M.ν i).w y := by
    by_cases hpy : 0 < Pi.w y
    · have hform : (tagPosterior6 M y).w i =
          M.Λ i * (M.ν i).w y / Pi.w y := by
        simp [tagPosterior6, Pi, hpy]
      rw [hform]
      field_simp [ne_of_gt hpy]
    · have hpy0 : Pi.w y = 0 := le_antisymm (le_of_not_gt hpy) (Pi.nonneg y)
      have hsum : ∑ j, M.Λ j * (M.ν j).w y = 0 := by
        simpa [Pi, secondMixture6, Law.mix, tagLaw6] using hpy0
      have hterm (j : M.ι) : M.Λ j * (M.ν j).w y = 0 := by
        have hz := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => mul_nonneg (M.Λ_nonneg j) ((M.ν j).nonneg y))).1 hsum
        exact hz j (Finset.mem_univ j)
      simp [hpy0, hterm i]
  have hBayesPoint (x : Fin N) (y : Fin N) :
      Pi.w y * (broadLaw6 M y).w x =
        ∑ i, (M.Λ i * (M.ν i).w y) * (M.μ i).w x := by
    change Pi.w y * (∑ i, (tagPosterior6 M y).w i * (M.μ i).w x) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      Pi.w y * ((tagPosterior6 M y).w i * (M.μ i).w x) =
          (Pi.w y * (tagPosterior6 M y).w i) * (M.μ i).w x := by ring
      _ = (M.Λ i * (M.ν i).w y) * (M.μ i).w x := by rw [hPostNum y i]
  have hBayes (x : Fin N) :
      ∑ y, Pi.w y * (broadLaw6 M y).w x = ∑ i, M.Λ i * (M.μ i).w x := by
    calc
      ∑ y, Pi.w y * (broadLaw6 M y).w x =
          ∑ y, ∑ i, (M.Λ i * (M.ν i).w y) * (M.μ i).w x := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hBayesPoint x y
      _ = ∑ i, ∑ y, (M.Λ i * (M.ν i).w y) * (M.μ i).w x := by
            rw [Finset.sum_comm]
      _ = ∑ i, M.Λ i * (M.μ i).w x := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              ∑ y, (M.Λ i * (M.ν i).w y) * (M.μ i).w x =
                  (M.Λ i * (M.μ i).w x) * ∑ y, (M.ν i).w y := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro y hy
                    ring
              _ = M.Λ i * (M.μ i).w x := by simp [(M.ν i).sum_eq_one]
  have hPosteriorSupport (y : Fin N) (i : M.ι)
      (hη : (tagPosterior6 M y).w i ≠ 0) : 0 < M.Λ i := by
    by_cases hpy : 0 < Pi.w y
    · have hform : (tagPosterior6 M y).w i =
          M.Λ i * (M.ν i).w y / Pi.w y := by
        simp [tagPosterior6, Pi, hpy]
      by_contra hΛ
      have hΛ0 : M.Λ i = 0 := le_antisymm (le_of_not_gt hΛ) (M.Λ_nonneg i)
      simp [hform, hΛ0] at hη
    · have hpy0 : Pi.w y = 0 := le_antisymm (le_of_not_gt hpy) (Pi.nonneg y)
      have hΛne : M.Λ i ≠ 0 := by
        simpa [tagPosterior6, Pi, hpy, hpy0, tagLaw6] using hη
      exact lt_of_le_of_ne (M.Λ_nonneg i) (Ne.symm hΛne)
  have hBroadWidth (y : Fin N) : (broadLaw6 M y).WidthLE ((n : ℝ) ^ γ) := by
    intro x
    change (∑ i, (tagPosterior6 M y).w i * (M.μ i).w x) ≤ _
    calc
      ∑ i, (tagPosterior6 M y).w i * (M.μ i).w x ≤
          ∑ i, (tagPosterior6 M y).w i * (Real.exp ((n : ℝ) ^ γ) / N) := by
            apply Finset.sum_le_sum
            intro i hi
            by_cases hη : (tagPosterior6 M y).w i = 0
            · simp [hη]
            · exact mul_le_mul_of_nonneg_left
                (hWidth i (hPosteriorSupport y i hη) x)
                ((tagPosterior6 M y).nonneg i)
      _ = Real.exp ((n : ℝ) ^ γ) / N := by
            rw [← Finset.sum_mul]
            simp [(tagPosterior6 M y).sum_eq_one]
  let H := heavySet6 (n := n) Dstar₆ Pi
  let U := Finset.univ \ H
  let massH := ∑ y ∈ H, Pi.w y
  have hdisj : Disjoint H U := by
    rw [Finset.disjoint_left]
    intro y hy hcomp
    exact (Finset.mem_sdiff.mp hcomp).2 hy
  have hUnion : H ∪ U = Finset.univ := by
    ext y
    simp [U]
  have hmassSplit : massH + (∑ y ∈ U, Pi.w y) = 1 := by
    dsimp [massH]
    rw [← Finset.sum_union hdisj, hUnion]
    exact Pi.sum_eq_one
  have hUnheavyAtom (y : Fin N) (hy : y ∉ H) :
      Pi.w y ≤ (n : ℝ) ^ (-Dstar₆) / N := by
    have hnot : ¬ (n : ℝ) ^ (-Dstar₆) ≤ (N : ℝ) * Pi.w y := by
      intro h
      apply hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have hlt : (N : ℝ) * Pi.w y < (n : ℝ) ^ (-Dstar₆) := lt_of_not_ge hnot
    exact (le_div_iff₀ hNpos).2 (le_of_lt (by nlinarith [hlt]))
  have hUcard : (U.card : ℝ) ≤ (N : ℝ) := by
    simpa using (Finset.card_le_card (Finset.subset_univ U))
  have hUnheavyMass : (∑ y ∈ U, Pi.w y) ≤ (n : ℝ) ^ (-Dstar₆) := by
    calc
      (∑ y ∈ U, Pi.w y) ≤ ∑ y ∈ U, (n : ℝ) ^ (-Dstar₆) / N := by
        apply Finset.sum_le_sum
        intro y hy
        exact hUnheavyAtom y (Finset.mem_sdiff.mp hy).2
      _ = (U.card : ℝ) * ((n : ℝ) ^ (-Dstar₆) / N) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * ((n : ℝ) ^ (-Dstar₆) / N) :=
        mul_le_mul_of_nonneg_right hUcard (div_nonneg (by positivity) (by positivity))
      _ = (n : ℝ) ^ (-Dstar₆) := by field_simp [ne_of_gt hNpos]
  have hmassRetained : 1 - (n : ℝ) ^ (-Dstar₆) ≤ massH := by
    linarith [hmassSplit, hUnheavyMass]
  have hmassHalf : (1 / 2 : ℝ) ≤ massH := by linarith [hmassRetained, hDsmall]
  have hmassEq : massH = ∑ y ∈ H, Pi.w y := rfl
  have hmassPos : 0 < ∑ y ∈ H, Pi.w y := by
    rw [← hmassEq]
    linarith [hmassHalf]
  let piPrime : Law N := Law.restrict Pi H hmassPos
  have hpiPrimeEq (y : Fin N) : piPrime.w y =
      if y ∈ H then Pi.w y / (∑ y' ∈ H, Pi.w y') else 0 := by
    simp [piPrime, Law.restrict]
  have hpiPrimeCap (y : Fin N) : piPrime.w y ≤ 2 * Pi.w y := by
    by_cases hy : y ∈ H
    · rw [hpiPrimeEq y, if_pos hy]
      apply (div_le_iff₀ hmassPos).2
      have hfactor : 1 ≤ 2 * (∑ y' ∈ H, Pi.w y') := by linarith [hmassHalf]
      nlinarith [Pi.nonneg y, hfactor]
    · rw [hpiPrimeEq y, if_neg hy]
      exact mul_nonneg (by norm_num) (Pi.nonneg y)
  have hEtaMean (i : M.ι) :
      ∑ y, Pi.w y * (tagPosterior6 M y).w i = M.Λ i := by
    calc
      ∑ y, Pi.w y * (tagPosterior6 M y).w i =
          ∑ y, M.Λ i * (M.ν i).w y := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hPostNum y i
      _ = M.Λ i := by
            rw [← Finset.mul_sum, (M.ν i).sum_eq_one]
            ring
  have hPiLowerHeavy (y : Fin N) (hy : y ∈ H) :
      (n : ℝ) ^ (-Dstar₆) / N ≤ Pi.w y := by
    have hmem : y ∈ heavySet6 (n := n) Dstar₆ Pi := by simpa [H] using hy
    apply (div_le_iff₀ hNpos).2
    nlinarith [(Finset.mem_filter.mp hmem).2]
  have hEtaCap (y : Fin N) (hy : y ∈ H) (i : M.ι) :
      (tagPosterior6 M y).w i ≤ (n : ℝ) ^ (2 * Dstar₆) * M.Λ i := by
    have hpowPos : 0 < (n : ℝ) ^ (-Dstar₆) := Real.rpow_pos_of_pos hnRpos _
    have hPiPos : 0 < Pi.w y := lt_of_lt_of_le (div_pos hpowPos hNpos) (hPiLowerHeavy y hy)
    by_cases hΛ : 0 < M.Λ i
    · have hform : (tagPosterior6 M y).w i =
          M.Λ i * (M.ν i).w y / Pi.w y := by
        simp [tagPosterior6, Pi, hPiPos]
      have hNum : (M.ν i).w y ≤ (n : ℝ) ^ Dstar₆ / N := by
        apply (le_div_iff₀ hNpos).2
        nlinarith [hCap i hΛ y]
      have hDen : (n : ℝ) ^ (-Dstar₆) / N ≤ Pi.w y := hPiLowerHeavy y hy
      have hRpow : (n : ℝ) ^ (2 * Dstar₆) * (n : ℝ) ^ (-Dstar₆) =
          (n : ℝ) ^ Dstar₆ := by
        rw [← Real.rpow_add hnRpos]
        congr 1 <;> ring
      have hmul : M.Λ i * ((n : ℝ) ^ Dstar₆ / N) ≤
          ((n : ℝ) ^ (2 * Dstar₆) * M.Λ i) * Pi.w y := by
        have hfacNonneg : 0 ≤ (n : ℝ) ^ (2 * Dstar₆) * M.Λ i :=
          mul_nonneg (Real.rpow_nonneg (by positivity) _) (M.Λ_nonneg i)
        have hdenMul := mul_le_mul_of_nonneg_left hDen hfacNonneg
        calc
          M.Λ i * ((n : ℝ) ^ Dstar₆ / N) =
              ((n : ℝ) ^ (2 * Dstar₆) * M.Λ i) * ((n : ℝ) ^ (-Dstar₆) / N) := by
                rw [div_eq_mul_inv, div_eq_mul_inv, ← hRpow]
                ring
          _ ≤ ((n : ℝ) ^ (2 * Dstar₆) * M.Λ i) * Pi.w y := hdenMul
      rw [hform]
      apply (div_le_iff₀ hPiPos).2
      calc
        M.Λ i * (M.ν i).w y ≤ M.Λ i * ((n : ℝ) ^ Dstar₆ / N) :=
          mul_le_mul_of_nonneg_left hNum (M.Λ_nonneg i)
        _ ≤ ((n : ℝ) ^ (2 * Dstar₆) * M.Λ i) * Pi.w y := hmul
    · have hΛ0 : M.Λ i = 0 := le_antisymm (le_of_not_gt hΛ) (M.Λ_nonneg i)
      simp [tagPosterior6, Pi, hPiPos, hΛ0]
  let badSet : Fin N → Finset (Fin N) := fun y =>
    Finset.univ.filter fun z => colDeg E G (broadLaw6 M y) z < c₀
  let badRows : Fin N → ℝ := fun y => ∑ z ∈ badSet y, piPrime.w z
  let badMass : ℝ := ∑ y, piPrime.w y * badRows y
  let S₁ := Finset.univ.filter fun y => (1 / 20 : ℝ) ≤ badRows y
  let V₁ := Finset.univ \ S₁
  let massS₁ : ℝ := ∑ y ∈ S₁, piPrime.w y
  let massV₁ : ℝ := ∑ y ∈ V₁, piPrime.w y
  have hbadRowsNonneg (y : Fin N) : 0 ≤ badRows y := by
    apply Finset.sum_nonneg
    intro z hz
    exact piPrime.nonneg z
  have hbadRowsLe (y : Fin N) : badRows y ≤ 1 := by
    dsimp [badRows]
    calc
      (∑ z ∈ badSet y, piPrime.w z) ≤ ∑ z, piPrime.w z :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun z _ _ => piPrime.nonneg z)
      _ = 1 := piPrime.sum_eq_one
  have hS₁disj : Disjoint S₁ V₁ := by
    rw [Finset.disjoint_left]
    intro y hy hcomp
    exact (Finset.mem_sdiff.mp hcomp).2 hy
  have hS₁union : S₁ ∪ V₁ = Finset.univ := by
    ext y
    simp [V₁]
  have hS₁split : massS₁ + massV₁ = 1 := by
    dsimp [massS₁, massV₁]
    rw [← Finset.sum_union hS₁disj, hS₁union]
    exact piPrime.sum_eq_one
  have hbadSplit : badMass =
      (∑ y ∈ S₁, piPrime.w y * badRows y) +
        ∑ y ∈ V₁, piPrime.w y * badRows y := by
    dsimp [badMass]
    rw [← Finset.sum_union hS₁disj, hS₁union]
  have hbadBound : badMass ≤ massS₁ + (1 / 20 : ℝ) * massV₁ := by
    rw [hbadSplit]
    apply add_le_add
    · calc
        (∑ y ∈ S₁, piPrime.w y * badRows y) ≤
            ∑ y ∈ S₁, piPrime.w y * 1 := by
              apply Finset.sum_le_sum
              intro y hy
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left (hbadRowsLe y) (piPrime.nonneg y)
        _ = massS₁ := by simp [massS₁]
    · calc
        (∑ y ∈ V₁, piPrime.w y * badRows y) ≤
            ∑ y ∈ V₁, piPrime.w y * (1 / 20 : ℝ) := by
              apply Finset.sum_le_sum
              intro y hy
              have hyNot : y ∉ S₁ := (Finset.mem_sdiff.mp hy).2
              have hlt : badRows y < 1 / 20 := lt_of_not_ge (by
                intro hmem
                exact hyNot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩))
              exact mul_le_mul_of_nonneg_left hlt.le (piPrime.nonneg y)
        _ = (1 / 20 : ℝ) * massV₁ := by
              rw [← Finset.sum_mul]
              simp [massV₁, mul_comm]
  have hColorDegSum (μ : Law N) (z : Fin N) :
      colDeg E G μ z + colDeg E (!G) μ z = 1 := by
    let f : Fin N → ℝ := fun x => μ.w x * (if Hits E G x z then 1 else 0)
    let g : Fin N → ℝ := fun x => μ.w x * (if Hits E (!G) x z then 1 else 0)
    have hterm (x : Fin N) : f x + g x = μ.w x := by
      cases G <;> by_cases h : E x z <;> simp [f, g, Hits, h]
    unfold colDeg
    calc
      (Finset.univ.sum f) + (Finset.univ.sum g) =
          Finset.univ.sum (fun x => f x + g x) := by
            symm
            exact Finset.sum_add_distrib
      _ = Finset.univ.sum μ.w := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hterm x
      _ = 1 := μ.sum_eq_one
  let goodSet : Fin N → Finset (Fin N) := fun y =>
    Finset.univ.filter fun z => (95 : ℝ) / 100 ≤ colDeg E (!G) (broadLaw6 M y) z
  have hBadToGood (y z : Fin N) (hz : z ∈ badSet y) : z ∈ goodSet y := by
    have hbad : colDeg E G (broadLaw6 M y) z < 1 / 100 := by
      simpa [badSet, c₀] using (Finset.mem_filter.mp hz).2
    have hsum := hColorDegSum (broadLaw6 M y) z
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    linarith
  by_cases hBadLarge : (1 / 10 : ℝ) ≤ badMass
  · have hmassS₁Nonneg : 0 ≤ massS₁ := by
      dsimp [massS₁]
      exact Finset.sum_nonneg fun y hy => piPrime.nonneg y
    have hmassV₁Nonneg : 0 ≤ massV₁ := by
      dsimp [massV₁]
      exact Finset.sum_nonneg fun y hy => piPrime.nonneg y
    have hmassS₁Lower : (1 / 20 : ℝ) ≤ massS₁ := by
      nlinarith [hBadLarge, hbadBound, hS₁split, hmassS₁Nonneg, hmassV₁Nonneg]
    have hS₁pos : 0 < massS₁ := lt_of_lt_of_le (by norm_num) hmassS₁Lower
    let rho : Law N := Law.restrict piPrime S₁ hS₁pos
    have hrhoEq (y : Fin N) : rho.w y =
        if y ∈ S₁ then piPrime.w y / massS₁ else 0 := by
      simp [rho, Law.restrict, massS₁]
    have hrhoDom (y : Fin N) : rho.w y ≤ 20 * piPrime.w y := by
      by_cases hy : y ∈ S₁
      · rw [hrhoEq y, if_pos hy]
        apply (div_le_iff₀ hS₁pos).2
        have hfactor : 1 ≤ 20 * massS₁ := by linarith [hmassS₁Lower]
        nlinarith [piPrime.nonneg y, hfactor]
      · rw [hrhoEq y, if_neg hy]
        exact mul_nonneg (by norm_num) (piPrime.nonneg y)
    have hpiAvg (x : Fin N) :
        (N : ℝ) * ∑ y, rho.w y * (broadLaw6 M y).w x ≤ 40 * K := by
      have hrhoPi (y : Fin N) : rho.w y ≤ 40 * Pi.w y := by
        calc
          rho.w y ≤ 20 * piPrime.w y := hrhoDom y
          _ ≤ 20 * (2 * Pi.w y) := mul_le_mul_of_nonneg_left
            (hpiPrimeCap y) (by norm_num)
          _ = 40 * Pi.w y := by ring
      have hsum : ∑ y, rho.w y * (broadLaw6 M y).w x ≤
          40 * ∑ y, Pi.w y * (broadLaw6 M y).w x := by
        calc
          ∑ y, rho.w y * (broadLaw6 M y).w x ≤
              ∑ y, (40 * Pi.w y) * (broadLaw6 M y).w x := by
                apply Finset.sum_le_sum
                intro y hy
                exact mul_le_mul_of_nonneg_right (hrhoPi y) ((broadLaw6 M y).nonneg x)
          _ = 40 * ∑ y, Pi.w y * (broadLaw6 M y).w x := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y hy
                ring
      have hmean : (N : ℝ) * ∑ y, Pi.w y * (broadLaw6 M y).w x ≤ K := by
        rw [hBayes x]
        exact hBal.1 x
      calc
        (N : ℝ) * ∑ y, rho.w y * (broadLaw6 M y).w x ≤
            (N : ℝ) * (40 * ∑ y, Pi.w y * (broadLaw6 M y).w x) :=
              mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N)
        _ = 40 * ((N : ℝ) * ∑ y, Pi.w y * (broadLaw6 M y).w x) := by ring
        _ ≤ 40 * K := mul_le_mul_of_nonneg_left hmean (by norm_num)
    let M₁ : TagMix N := {
      ι := Fin N
      Λ := rho.w
      Λ_nonneg := rho.nonneg
      Λ_sum := rho.sum_eq_one
      μ := fun y => broadLaw6 M y
      ν := fun y => broadLaw6 M y }
    have hM₁Balanced : M₁.Balanced (40 * K) := by
      constructor
      · intro x
        simpa [M₁] using hpiAvg x
      · intro y
        simpa [M₁] using hpiAvg y
    have hM₁Width : ∀ y, 0 < M₁.Λ y → (M₁.μ y).WidthLE ((n : ℝ) ^ γ) := by
      intro y hy
      exact hBroadWidth y
    have hM₁Good : ∀ y, 0 < M₁.Λ y →
        (1 / (40 * K) : ℝ) * N ≤ (goodSet y).card := by
      intro y hy
      have hyS₁ : y ∈ S₁ := by
        by_contra hyS₁
        have hyzero : rho.w y = 0 := by simp [hrhoEq y, hyS₁]
        exact (ne_of_gt (by simpa [M₁] using hy)) hyzero
      have hrow : (1 / 20 : ℝ) ≤ badRows y := (Finset.mem_filter.mp hyS₁).2
      have hrowUpper : badRows y ≤ (badSet y).card * (2 * K / N) := by
        calc
          badRows y ≤ ∑ z ∈ badSet y, (2 * K / N) := by
            apply Finset.sum_le_sum
            intro z hz
            have hPiAtom : Pi.w z ≤ K / N := by
              apply (le_div_iff₀ hNpos).2
              nlinarith [hPiCap z]
            calc
              piPrime.w z ≤ 2 * Pi.w z := hpiPrimeCap z
              _ ≤ 2 * (K / N) := by nlinarith [hPiAtom]
              _ = 2 * K / N := by ring
          _ = (badSet y).card * (2 * K / N) := by
            simp [badRows, Finset.sum_const, nsmul_eq_mul]
      have hrowDiv : (1 / 20 : ℝ) ≤ ((badSet y).card * (2 * K)) / N := by
        have hEq : (badSet y).card * (2 * K / N) =
            ((badSet y).card * (2 * K)) / N := by ring
        linarith [hrow, hrowUpper, hEq]
      have hrowN : (1 / 20 : ℝ) * N ≤ (badSet y).card * (2 * K) :=
        (le_div_iff₀ hNpos).1 hrowDiv
      have hcard : (1 / (40 * K) : ℝ) * N ≤ (badSet y).card := by
        rw [show (1 / (40 * K) : ℝ) * N = (N : ℝ) / (40 * K) by ring]
        apply (div_le_iff₀ hK40).2
        nlinarith [hrowN]
      have hsubset : badSet y ⊆ goodSet y := hBadToGood y
      exact hcard.trans (by exact_mod_cast Finset.card_le_card hsubset)
    have hcube := hL5 n N E (!G) (Fin N) M₁.Λ M₁.μ hLarge5
      M₁.Λ_nonneg M₁.Λ_sum hM₁Width hM₁Balanced.1 hM₁Good
    exact Or.inl hcube
  · have hComplementCase : badMass < 1 / 10 := lt_of_not_ge hBadLarge
    have hPrComplement (P : Law N) (A : Fin N → Prop) :
        P.pr A + P.pr (fun ω => ¬ A ω) = 1 := by
      rw [FinProb.pr_compl5]
      ring
    let badPred : Fin N → Fin N → Prop := fun y z =>
      colDeg E G (broadLaw6 M y) z < c₀
    have hBadRowsPr (y : Fin N) : badRows y =
        FinProb.pr piPrime (fun z => badPred y z) := by
      simp [badRows, badSet, badPred, FinProb.pr, Finset.sum_filter]
    let revRows : Fin N → ℝ := fun y => FinProb.pr piPrime (fun z => badPred z y)
    let relRows : Fin N → ℝ := fun y => FinProb.pr piPrime (fun z => related6 E G M y z)
    let nonRelRows : Fin N → ℝ := fun y => FinProb.pr piPrime (fun z => ¬ related6 E G M y z)
    let relMass : ℝ := ∑ y, piPrime.w y * relRows y
    let nonRelMass : ℝ := ∑ y, piPrime.w y * nonRelRows y
    let revMass : ℝ := ∑ y, piPrime.w y * revRows y
    have hNotRelPred (y z : Fin N) (h : ¬ related6 E G M y z) :
        badPred y z ∨ badPred z y := by
      by_cases hleft : badPred y z
      · exact Or.inl hleft
      · right
        by_contra hright
        apply h
        exact ⟨le_of_not_gt hleft, le_of_not_gt hright⟩
    have hRevRowsCond (y : Fin N) : revRows y =
        ∑ z, if badPred z y then piPrime.w z else 0 := by
      simp [revRows, FinProb.pr]
    have hBadRowsCond (y : Fin N) : badRows y =
        ∑ z, if badPred y z then piPrime.w z else 0 := by
      rw [hBadRowsPr y]
      simp [FinProb.pr]
    have hNonRelRowBound (y : Fin N) :
        nonRelRows y ≤ badRows y + revRows y := by
      calc
        nonRelRows y = FinProb.pr piPrime (fun z => ¬ related6 E G M y z) := rfl
        _ ≤ FinProb.pr piPrime (fun z => badPred y z ∨ badPred z y) :=
          FinProb.pr_mono5 piPrime (fun z hz => hNotRelPred y z hz)
        _ ≤ FinProb.pr piPrime (fun z => badPred y z) +
              FinProb.pr piPrime (fun z => badPred z y) :=
          FinProb.pr_union piPrime (fun z => badPred y z) (fun z => badPred z y)
        _ = badRows y + revRows y := by
          rw [← hBadRowsPr y]
    have hRevMass : revMass = badMass := by
      have hExpand : Finset.univ.sum (fun y : Fin N => piPrime.w y * revRows y) =
          Finset.univ.sum (fun y : Fin N => Finset.univ.sum (fun z : Fin N =>
            (if badPred z y then piPrime.w y * piPrime.w z else 0))) := by
        apply Finset.sum_congr rfl
        intro y hy
        calc
          piPrime.w y * revRows y =
              piPrime.w y * Finset.univ.sum (fun z : Fin N =>
                if badPred z y then piPrime.w z else 0) := by
                rw [hRevRowsCond y]
          _ = Finset.univ.sum (fun z : Fin N =>
                (if badPred z y then piPrime.w y * piPrime.w z else 0)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro z hz
                by_cases hbad : badPred z y <;> simp [hbad, mul_comm]
      calc
        revMass = Finset.univ.sum (fun y : Fin N => Finset.univ.sum (fun z : Fin N =>
            (if badPred z y then piPrime.w y * piPrime.w z else 0))) := by
          simpa [revMass] using hExpand
        _ = Finset.univ.sum (fun z : Fin N => Finset.univ.sum (fun y : Fin N =>
            (if badPred z y then piPrime.w y * piPrime.w z else 0))) := by
          rw [Finset.sum_comm]
        _ = Finset.univ.sum (fun z : Fin N => piPrime.w z * badRows z) := by
          apply Finset.sum_congr rfl
          intro z hz
          calc
            Finset.univ.sum (fun y : Fin N =>
                (if badPred z y then piPrime.w y * piPrime.w z else 0)) =
                piPrime.w z * Finset.univ.sum (fun y : Fin N =>
                  (if badPred z y then piPrime.w y else 0)) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro y hy
                  by_cases hbad : badPred z y <;> simp [hbad, mul_comm]
            _ = piPrime.w z * badRows z := by rw [← hBadRowsCond z]
        _ = badMass := rfl
    have hNonRelAvgBound : nonRelMass ≤ 2 * badMass := by
      calc
        nonRelMass ≤ ∑ y, piPrime.w y * (badRows y + revRows y) := by
          apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul_of_nonneg_left (hNonRelRowBound y) (piPrime.nonneg y)
        _ = badMass + revMass := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
        _ = 2 * badMass := by rw [hRevMass]; ring
    have hRowsSplit (y : Fin N) : relRows y + nonRelRows y = 1 := by
      have h := hPrComplement piPrime (fun z => related6 E G M y z)
      simpa [relRows, nonRelRows] using h
    have hPairSplit : relMass + nonRelMass = 1 := by
      calc
        relMass + nonRelMass =
            ∑ y, piPrime.w y * (relRows y + nonRelRows y) := by
              dsimp [relMass, nonRelMass]
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro y hy
              ring
        _ = ∑ y, piPrime.w y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hRowsSplit y]
          ring
        _ = 1 := piPrime.sum_eq_one
    have hRelMass : (4 / 5 : ℝ) ≤ relMass := by
      linarith [hPairSplit, hNonRelAvgBound, hComplementCase]
    have hPrNonneg (P : FinProb (Fin N)) (A : Fin N → Prop) : 0 ≤ P.pr A := by
      unfold FinProb.pr
      apply Finset.sum_nonneg
      intro y hy
      by_cases hA : A y <;> simp [hA, P.nonneg y]
    have hPrLeOne (P : FinProb (Fin N)) (A : Fin N → Prop) : P.pr A ≤ 1 := by
      have hcompl := hPrComplement P A
      have hnonneg := hPrNonneg P (fun y => ¬ A y)
      linarith
    let T₀ := Finset.univ.filter fun y : Fin N => (1 / 10 : ℝ) ≤ relRows y
    let V₀ := Finset.univ \ T₀
    let massT₀ : ℝ := ∑ y ∈ T₀, piPrime.w y
    let massV₀ : ℝ := ∑ y ∈ V₀, piPrime.w y
    have hT₀disj : Disjoint T₀ V₀ := by
      rw [Finset.disjoint_left]
      intro y hy hcomp
      exact (Finset.mem_sdiff.mp hcomp).2 hy
    have hT₀union : T₀ ∪ V₀ = Finset.univ := by
      ext y
      simp [V₀]
    have hT₀split : massT₀ + massV₀ = 1 := by
      dsimp [massT₀, massV₀]
      rw [← Finset.sum_union hT₀disj, hT₀union]
      exact piPrime.sum_eq_one
    have hRelSplit : relMass =
        (∑ y ∈ T₀, piPrime.w y * relRows y) +
          ∑ y ∈ V₀, piPrime.w y * relRows y := by
      dsimp [relMass]
      rw [← hT₀union, ← Finset.sum_union hT₀disj]
    have hRelBound : relMass ≤ massT₀ + (1 / 10 : ℝ) * massV₀ := by
      rw [hRelSplit]
      apply add_le_add
      · apply Finset.sum_le_sum
        intro y hy
        simpa [relRows] using mul_le_mul_of_nonneg_left
          (hPrLeOne piPrime (fun z => related6 E G M y z)) (piPrime.nonneg y)
      · calc
          (∑ y ∈ V₀, piPrime.w y * relRows y) ≤
              ∑ y ∈ V₀, piPrime.w y * (1 / 10 : ℝ) := by
                apply Finset.sum_le_sum
                intro y hy
                have hnotT : y ∉ T₀ := (Finset.mem_sdiff.mp hy).2
                have hnot : ¬ (1 / 10 : ℝ) ≤ relRows y := by
                  intro hrel
                  exact hnotT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrel⟩)
                have hlt : relRows y < 1 / 10 := lt_of_not_ge hnot
                simpa [relRows] using mul_le_mul_of_nonneg_left hlt.le (piPrime.nonneg y)
          _ = (1 / 10 : ℝ) * massV₀ := by
                rw [← Finset.sum_mul]
                simp [massV₀, mul_comm]
    have hmassT₀Lower : (7 / 10 : ℝ) ≤ massT₀ := by
      nlinarith [hRelMass, hRelBound, hT₀split]
    let S₀ := H.filter fun y => (1 / 10 : ℝ) ≤ relRows y
    have hS₀subset : S₀ ⊆ T₀ := by
      intro y hy
      simp only [S₀, Finset.mem_filter] at hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.2⟩
    have hpiPrimeZero (y : Fin N) (hy : y ∉ H) : piPrime.w y = 0 := by
      rw [hpiPrimeEq y]
      simp [hy]
    have hmassS₀Eq : massT₀ = ∑ y ∈ S₀, piPrime.w y := by
      dsimp [massT₀]
      symm
      apply Finset.sum_subset hS₀subset
      intro y hy hnot
      have hyH : y ∉ H := by
        intro hmem
        exact hnot (Finset.mem_filter.mpr ⟨hmem, (Finset.mem_filter.mp hy).2⟩)
      exact hpiPrimeZero y hyH
    have hS₀mass : (7 / 10 : ℝ) ≤ ∑ y ∈ S₀, piPrime.w y := by
      rw [← hmassS₀Eq]
      exact hmassT₀Lower
    have hpartnerMass (y : Fin N) (hy : y ∈ S₀) :
        (1 / 10 : ℝ) ≤ FinProb.pr piPrime (fun z => related6 E G M y z) := by
      simpa [S₀, relRows] using (Finset.mem_filter.mp hy).2
    have hpartnerFormula (y : Fin N) (hy : y ∈ S₀) (f z : Fin N) :
        (partnerLaw6 piPrime (related6 E G M) y f).w z =
          if related6 E G M y z then piPrime.w z / relRows y else 0 := by
      have hmax (z : Fin N) :
          max 0 (if related6 E G M y z then piPrime.w z else 0) =
            if related6 E G M y z then piPrime.w z else 0 := by
        split_ifs <;> [exact max_eq_right (piPrime.nonneg z); simp]
      have hsum :
          (∑ z, max 0 (if related6 E G M y z then piPrime.w z else 0)) = relRows y := by
        calc
          (∑ z, max 0 (if related6 E G M y z then piPrime.w z else 0)) =
              ∑ z, if related6 E G M y z then piPrime.w z else 0 := by
                apply Finset.sum_congr rfl
                intro z hz
                exact hmax z
          _ = FinProb.pr piPrime (fun z => related6 E G M y z) := by
                rfl
          _ = relRows y := by rfl
      have hden : 0 < ∑ z, max 0
          (if related6 E G M y z then piPrime.w z else 0) := by
        rw [hsum]
        exact lt_of_lt_of_le (by norm_num) (hpartnerMass y hy)
      unfold partnerLaw6 restrictOr6
      unfold normalize6
      dsimp
      split
      · dsimp
        rw [hsum]
        by_cases hrel : related6 E G M y z <;> simp [hrel, piPrime.nonneg z]
      · rename_i hpos
        exact False.elim (hpos hden)
    have hpartnerCap (y : Fin N) (hy : y ∈ S₀) (f z : Fin N) :
        (partnerLaw6 piPrime (related6 E G M) y f).w z ≤ 20 * Pi.w z := by
      rw [hpartnerFormula y hy f z]
      by_cases hrel : related6 E G M y z
      · rw [if_pos hrel]
        have hden : (1 / 10 : ℝ) ≤ relRows y := (Finset.mem_filter.mp hy).2
        have hnorm : piPrime.w z / relRows y ≤ 10 * piPrime.w z := by
          apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)).2
          nlinarith [piPrime.nonneg z, hden]
        calc
          piPrime.w z / relRows y ≤ 10 * piPrime.w z := hnorm
          _ ≤ 10 * (2 * Pi.w z) := mul_le_mul_of_nonneg_left (hpiPrimeCap z) (by norm_num)
          _ = 20 * Pi.w z := by ring
      · rw [if_neg hrel]
        exact mul_nonneg (by norm_num) (Pi.nonneg z)
    right
    refine ⟨{
      heavy := H
      heavy_eq := by simp [H, Pi]
      piPrime := piPrime
      retained_mass := by simpa [H, Pi, massH] using hmassRetained
      piPrime_eq := by simpa [Pi] using hpiPrimeEq
      piPrime_cap := by simpa [Pi] using hpiPrimeCap
      eta_cap := by simpa [H, Pi] using hEtaCap
      eta_mean := by simpa [Pi] using hEtaMean
      broad_width := fun y hy => hBroadWidth y
      S₀ := S₀
      S₀_eq := by
        ext y
        simp [S₀, H, Pi, relRows]
      S₀_mass := by
        let p : Fin N → Prop := fun y => y ∈ S₀
        let f : Fin N → ℝ := fun y => if p y then piPrime.w y else 0
        calc
          (7 / 10 : ℝ) ≤ ∑ y ∈ S₀, piPrime.w y := hS₀mass
          _ = ∑ y ∈ S₀, f y := by
            apply Finset.sum_congr rfl
            intro y hy
            simp [f, p, hy]
          _ ≤ ∑ y, f y := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S₀)
            intro y hy hnot
            simp [f, p, hnot]
          _ = FinProb.pr piPrime (fun y => y ∈ S₀) := by
            unfold FinProb.pr
            apply Finset.sum_congr rfl
            intro y hy
            simp [f, p]
      partner_mass := hpartnerMass
      partner_cap := by simpa [Pi] using hpartnerCap
    }⟩

end

end S06
end HypercubeRamsey
