import HypercubeRamsey.S08.L81.Grid
import HypercubeRamsey.S08.L81.Prelude

/-!
# Lemma 8.1, Step 1: trimming to nearly constant survival

Source: `sections/08-…tex`, lines 23–46; blueprint L8.1b.

`excMass x = Λ{i : |d_G(x, ν_i) - 1/2| > 2n^{-η}}`; the dropped set `D` is the set of `x ∈ X` with
`excMass x > e^{-n^η/2}`; the kept tags are those with `μ_i(D) ≤ 1/2`; the trimmed mixture restricts the tag law to
the kept tags and each first law to `Dᶜ`, both normalized (08:31–39).  The trimmed data, together with the fixed
exponents and the tuple length `h`, form the context `Ctx` used by every later step; `Std` records what Step 1
delivers about it.
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- The one-shot hypotheses of Lemma 8.1 at one dimension (`asymmetric_purity`), with the large regime reduced
to `N ≤ n 2^n`. -/
structure Input (η₀ γ β p K : ℝ) (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
    (G : Colour) (M : TagMix N) : Prop where
  size : N ≤ n * 2 ^ n
  disc : DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀))
  bal : M.Balanced K
  laws : ∀ i, 0 < M.Λ i →
    (M.μ i).SupportedIn X ∧ (M.ν i).SupportedIn Y ∧
    (M.μ i).WidthLE ((n : ℝ) ^ γ) ∧ (M.ν i).WidthLE ((n : ℝ) ^ β) ∧
    ∀ y, 0 < (M.ν i).w y → 1 - Real.exp (-((n : ℝ) ^ p)) ≤ colDeg E G (M.μ i) y

section Trim

variable (η₀ : ℝ) (n : ℕ) {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (X : Finset (Fin N))
  (M : TagMix N)

/-- The exceptional event `|d_G(x, ν) - 1/2| > 2n^{-η}` (08:31). -/
def Exc (x : Fin N) (ν : Law N) : Prop :=
  2 * (n : ℝ) ^ (-eta8 η₀) < |rowDeg E G x ν - 1 / 2|

/-- `b(x) = Λ{i : exceptional}` (08:31). -/
def excMass (x : Fin N) : ℝ := ∑ i, M.Λ i * if Exc η₀ n E G x (M.ν i) then 1 else 0

/-- The dropped first-side labels `D = {x ∈ X : b(x) > e^{-n^η/2}}` (08:36). -/
def dropSet : Finset (Fin N) :=
  X.filter fun x => Real.exp (-(n : ℝ) ^ eta8 η₀ / 2) < excMass η₀ n E G M x

/-- The retained first-side labels `X \ D`. -/
def retained : Finset (Fin N) := X \ dropSet η₀ n E G X M

/-- A tag is kept when `μ_i(D) ≤ 1/2` (08:39). -/
def Keep (i : M.ι) : Prop := ∑ x ∈ dropSet η₀ n E G X M, (M.μ i).w x ≤ 1 / 2

/-- The trimmed tag law: `Λ` restricted to the kept tags, normalized (`Λ` itself if no tag is kept). -/
def trimΛ : FinProb M.ι :=
  normOr (fun i => M.Λ i * if Keep η₀ n E G X M i then 1 else 0)
    (fun i => mul_nonneg (M.Λ_nonneg i) (by split_ifs <;> norm_num)) ⟨M.Λ, M.Λ_nonneg, M.Λ_sum⟩

/-- The trimmed first law: `μ_i` restricted to `Dᶜ`, normalized (`μ_i` itself at zero mass). -/
def trimμ (i : M.ι) : Law N :=
  normOr (fun x => (M.μ i).w x * if x ∈ dropSet η₀ n E G X M then 0 else 1)
    (fun x => mul_nonneg ((M.μ i).nonneg x) (by split_ifs <;> norm_num)) (M.μ i)

/-- The trimmed mixture (08:39–40): the same tags and second laws. -/
def trimMix : TagMix N where
  ι := M.ι
  Λ := (trimΛ η₀ n E G X M).w
  Λ_nonneg := (trimΛ η₀ n E G X M).nonneg
  Λ_sum := (trimΛ η₀ n E G X M).sum_eq_one
  μ := trimμ η₀ n E G X M
  ν := M.ν

end Trim

/-- The data of one application of L8.1 after trimming: the dimension, the host side, the colouring, the colour
and the trimmed mixture.  The fixed exponents `η₀, β, p` and the tuple length `h` are parameters. -/
structure Ctx (η₀ β p : ℝ) (h : ℕ) where
  n : ℕ
  N : ℕ
  E : Fin N → Fin N → Prop
  G : Colour
  M : TagMix N

/-- The trimmed context. -/
def trimCtx (η₀ β p : ℝ) (h n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Finset (Fin N))
    (M : TagMix N) : Ctx η₀ β p h :=
  ⟨n, N, E, G, trimMix η₀ n E G X M⟩

/-- What Step 1 delivers on a context (08:39–46): (7.2) on `(X, Y)`, balance `4K`, first laws on the retained
set `R ⊆ X` of width `n^γ + log 2`, second laws on `Y` of width `n^β`, own-colour defect `2e^{-n^p}`, and survival
`α_x = 2^{-h}(1 + θ_x)`, `|θ_x| ≤ n^{-η/2}`, for every retained `x`. -/
structure Std {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h) (γ K : ℝ) (X Y R : Finset (Fin D.N)) : Prop where
  size : 0 < D.N ∧ D.N ≤ D.n * 2 ^ D.n
  disc : DiscOne D.E X Y ((D.n : ℝ) ^ η₀) ((D.n : ℝ) ^ η₀) ((D.n : ℝ) ^ (-η₀))
  bal : D.M.Balanced (4 * K)
  ret : R ⊆ X
  laws : ∀ i, 0 < D.M.Λ i →
    (D.M.μ i).SupportedIn R ∧ (D.M.ν i).SupportedIn Y ∧
    (D.M.μ i).WidthLE ((D.n : ℝ) ^ γ + Real.log 2) ∧ (D.M.ν i).WidthLE ((D.n : ℝ) ^ β) ∧
    ∀ y, 0 < (D.M.ν i).w y → 1 - 2 * Real.exp (-((D.n : ℝ) ^ p)) ≤ colDeg D.E D.G (D.M.μ i) y
  survival : ∀ x ∈ R,
    |∑ i, D.M.Λ i * rowDeg D.E D.G x (D.M.ν i) ^ h - ((2 : ℝ) ^ h)⁻¹| ≤
      ((2 : ℝ) ^ h)⁻¹ * (D.n : ℝ) ^ (-(eta8 η₀ / 2))

/-- L8.1b(i) (08:29–39): for large `n`, (7.2) applied to the uniform law on either signed exceptional set of one
`ν_i` (width `≤ n^η ≤ n^{η₀}` once the set has at least `Ne^{-n^η}` labels, `ν_i` of width `n^β ≤ n^{η₀}`) bounds
its size by `Ne^{-n^η}`; hence `Σ_x b(x) ≤ 2Ne^{-n^η}`, `|D| ≤ 2Ne^{-n^η/2}`, `E_Λ μ_i(D) ≤ 2Ke^{-n^η/2}` and the
discarded tags have mass at most `4Ke^{-n^η/2}` (Markov). -/
theorem trim_drop (η₀ β K : ℝ) (hη₀ : 0 < η₀) (hβ₀ : 0 < β) (hβτ : β < tau8 η₀ / 4) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour)
      (M : TagMix N),
      DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) → M.Balanced K →
      (∀ i, 0 < M.Λ i → (M.ν i).SupportedIn Y ∧ (M.ν i).WidthLE ((n : ℝ) ^ β)) →
      ((dropSet η₀ n E G X M).card : ℝ) ≤ 2 * N * Real.exp (-(n : ℝ) ^ eta8 η₀ / 2) ∧
      1 - 4 * K * Real.exp (-(n : ℝ) ^ eta8 η₀ / 2) ≤
        ∑ i, M.Λ i * (if Keep η₀ n E G X M i then 1 else 0) := by
  sorry

/-- L8.1b(ii) (08:39–46): given the drop bounds, the trimmed context satisfies `Std` for large `n` (depending on
`h`): the kept mass is at least `1/2`, so balance at most doubles twice; kept first laws lose at most half their
mass (width `+ log 2`, defect `≤ 2ε`); a retained `x` has `|d_G(x, ν_i) - 1/2| ≤ 2n^{-η}` outside trimmed tag
mass `2e^{-n^η/2}`, so `α_x = 2^{-h}(1 + O(hn^{-η}) + O(2^h e^{-n^η/2}))`. -/
theorem trim_std_of (η₀ γ β p K : ℝ) (hη₀ : 0 < η₀) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hβ₀ : 0 < β)
    (hβτ : β < tau8 η₀ / 4) (hp : 0 < p) (hK : 0 < K) (h : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour)
      (M : TagMix N),
      Input η₀ γ β p K n N E X Y G M →
      ((dropSet η₀ n E G X M).card : ℝ) ≤ 2 * N * Real.exp (-(n : ℝ) ^ eta8 η₀ / 2) →
      1 - 4 * K * Real.exp (-(n : ℝ) ^ eta8 η₀ / 2) ≤
        ∑ i, M.Λ i * (if Keep η₀ n E G X M i then 1 else 0) →
      Std (trimCtx η₀ β p h n N E G X M) γ K X Y (retained η₀ n E G X M) := by
  sorry

/-- L8.1b assembled (08:23–46). -/
theorem trim_std (η₀ γ β p K : ℝ) (hη₀ : 0 < η₀) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hβ₀ : 0 < β)
    (hβτ : β < tau8 η₀ / 4) (hp : 0 < p) (hK : 0 < K) (h : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour)
      (M : TagMix N),
      Input η₀ γ β p K n N E X Y G M →
      Std (trimCtx η₀ β p h n N E G X M) γ K X Y (retained η₀ n E G X M) := by
  obtain ⟨n₁, hdrop⟩ := trim_drop η₀ β K hη₀ hβ₀ hβτ
  obtain ⟨n₂, hstd⟩ := trim_std_of η₀ γ β p K hη₀ hγ₀ hγ₁ hβ₀ hβτ hp hK h
  refine ⟨max n₁ n₂, fun n hn N E X Y G M hI => ?_⟩
  obtain ⟨hcard, hkeep⟩ := hdrop n (le_trans (le_max_left _ _) hn) N E X Y G M hI.disc hI.bal
    (fun i hi => ⟨(hI.laws i hi).2.1, (hI.laws i hi).2.2.2.1⟩)
  exact hstd n (le_trans (le_max_right _ _) hn) N E X Y G M hI hcard hkeep

end HypercubeRamsey.S08
