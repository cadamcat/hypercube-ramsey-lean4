import HypercubeRamsey.S06.Defs
import HypercubeRamsey.S05.Assembly

/-!
# Section 6 preliminary reduction

L6.1a (06:28–65).  Either the opposite colour already has a cube (Lemma 5.1 applied to the laws `B_y` in
colour `!G`), or the symmetric parent relation `y ≍ y'` has a broad core `S₀`.  The parent record fixes the
heavy support, `Π'`, the relation and the partner laws used by all later Section 6 nodes.

Repair note.  The frozen `L6_1a` took `n₀ C₀` as universally quantified inputs; it was refuted with
`n₀ = 0, C₀ = 1/4, n = 2, N = 1` (`runs/lanes/p-s06-a/REPORT.md`).  Lemma 5.1 and the heavy-support bounds need
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

/-- L6.1a (06:28–65): for `n` and `N/2^n` large, either some colour has a cube (Case 1 via Lemma 5.1 in colour
`!G`, with tags `y ∈ S₁`, laws `B_y`, balance `40K`, and `χ = 1/(40K)` good columns of degree `> .99`), or
the Case 2 parent record exists.  The degree hypothesis of Lemma 6.1 is not needed here. -/
theorem L6_1a (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ∃ (n₀ : ℕ) (C₀ : ℝ), 0 < C₀ ∧ ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N),
      LargeAt n₀ C₀ n N → M.Balanced K →
      (∀ i, 0 < M.Λ i → (M.μ i).WidthLE ((n : ℝ) ^ γ)) →
      (∀ i, 0 < M.Λ i → (M.ν i).CapLE ((n : ℝ) ^ Dstar₆)) →
      CubeAt n N E ∨ Nonempty (ParentCase6 n N E G M γ Dstar₆) := by
  sorry

end

end S06
end HypercubeRamsey
