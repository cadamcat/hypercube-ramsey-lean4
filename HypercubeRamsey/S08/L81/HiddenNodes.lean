import HypercubeRamsey.S08.L81.Facts

/-!
# Lemma 8.1, Steps 2 and 4: base gates and the fixed-presentation reference experiment

Source: `sections/08-…tex`, lines 48–123 (L8.1c) and 139–176 (L8.1e).
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

theorem eta8_pos {η₀ : ℝ} (hη₀ : 0 < η₀) : 0 < eta8 η₀ := lt_min (by linarith) (by norm_num)

theorem tau8_pos {η₀ : ℝ} (hη₀ : 0 < η₀) : 0 < tau8 η₀ := by
  rw [tau8_eq]; exact div_pos (eta8_pos hη₀) (by norm_num)

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

/-! ## L8.1c: base gates (08:76–123) -/

/-- L8.1c(G1) (08:83–89): the event `R'(Θ_g) < N^{-h} e^{-n^{τ/2}}` has probability at most `e^{-n^{τ/2}}` (there
are `N^h` tuples); outside it `η_g(i)/Λ(i) = ν_i^{⊗h}(Θ_g)/R'(Θ_g) ≤ e^{hn^β + n^{τ/2}}`, since `ν_i` has width
`n^β`. -/
theorem gate1_tail (hη₀ : 0 < η₀) (hβ₀ : 0 < β) :
    ∀ D : Ctx η₀ β p h, ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      ∀ g, D.rawHidden.pr (fun Θ => ¬ D.Gate1 Θ g) ≤ Real.exp (-(D.n : ℝ) ^ (tau8 η₀ / 2)) := by
  sorry

/-- One filtering step (08:99): if a first-side law on `X` has width at most `n^η` and a second-side law on `Y` has
width at most `n^β`, the second law puts mass at most `2e^{-n^η}` on labels whose hit fraction into the first law
is outside `1/2 ± 2n^{-η}`. -/
def FilterStep (η₀ β : ℝ) (n : ℕ) : Prop :=
  ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour) (μ ν : Law N),
    DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
    μ.SupportedIn X → μ.WidthLE ((n : ℝ) ^ eta8 η₀) → ν.SupportedIn Y → ν.WidthLE ((n : ℝ) ^ β) →
    (∑ y, ν.w y * if 2 * (n : ℝ) ^ (-eta8 η₀) < |colDeg E G μ y - 1 / 2| then 1 else 0) ≤
      2 * Real.exp (-(n : ℝ) ^ eta8 η₀)

/-- L8.1c, filtering step (08:99): restricting `ν` to either exceptional set, if that set had `ν`-mass at least
`e^{-n^η}`, would give a law of width at most `n^β + n^η ≤ n^{η₀}` whose density with `μ` differs from `1/2` by
more than `2n^{-η} ≥ n^{-η₀}`, contradicting (7.2). -/
theorem filter_step (hη₀ : 0 < η₀) (hβ₀ : 0 < β) (hβτ : β < tau8 η₀ / 4) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, FilterStep η₀ β n := by
  sorry

/-- L8.1c(G3–G4) (08:90–105): filter the aggregates `μ̄_η = ∫ μ_i dη_g` (on (G1), `N max μ̄_η ≤ 4K e^{hn^β +
n^{τ/2}}`) and `μ̄_Λ` (`N max ≤ 4K`) successively by the coordinates of the independent cross tuples.  Given a cross
tuple's latent tag its coordinates are independent with law `ν_i`; after at most `2hs` regular hits the filtered
aggregate still has width below `n^η`, so by `FilterStep` a next hit fraction outside `1/2 ± 2n^{-η}` has
probability at most `2e^{-n^η}`.  The products of fractions over `h|E(g)| ≤ 2hs` coordinates are
`A_g(1 + o(1))`, and with one key omitted `2^h A_g(1 + o(1))`; the union costs `O(hs²) e^{-n^η}`. -/
theorem gate34_tail (hη₀ : 0 < η₀) (hβ₀ : 0 < β) (hβτ : β < tau8 η₀ / 4) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      GridFacts η₀ D.n → FilterStep η₀ β D.n →
      ∀ g, D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ ¬ D.Gate34 Θ g) ≤
        Real.exp (-(D.n : ℝ) ^ (eta8 η₀ / 2)) := by
  sorry

/-- L8.1c(G2) (08:107–123): with `L_g = ∫ (d_i^- - d_i^+) dη_g`, the own-colour defect `2ε` and survival
`α_x^{|E(g)|} ≤ 1.1A_g` give `E[L_g | Θ_g] ≤ 2.2hεA_g`; Markov at `.1ΔA_g` fails with probability
`O(hε/Δ) = exp(-n^p + n^{p/2} + O_h(1))`.  On (G3), the cutoff `d^+ ≥ (1-Δ)d^-` removes at most `L_g/Δ ≤ .1A_g`,
the cutoff `d^- ≥ e^{-n^{2τ}}` removes at most `e^{-n^{2τ}} = o(A_g)` (`log A_g^{-1} = O(hs)`), so
`.8A_g ≤ Z_g ≤ 1.2A_g`. -/
theorem gate2_tail (hη₀ : 0 < η₀) (hp : 0 < p) (hK : 0 < K) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      ∀ g, D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ D.Gate34 Θ g ∧ ¬ D.Gate2 Θ g) ≤
        Real.exp (-(D.n : ℝ) ^ c) := by
  sorry

/-- L8.1c, union bound (08:76): three stretched-exponential tails at exponents `a, b, c` give a base-gate tail at
exponent `min(a, b, c)/2` for large `n`. -/
theorem gate_tail_of (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n →
      (∀ g, D.rawHidden.pr (fun Θ => ¬ D.Gate1 Θ g) ≤ Real.exp (-(D.n : ℝ) ^ a)) →
      (∀ g, D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ ¬ D.Gate34 Θ g) ≤ Real.exp (-(D.n : ℝ) ^ b)) →
      (∀ g, D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ D.Gate34 Θ g ∧ ¬ D.Gate2 Θ g) ≤
        Real.exp (-(D.n : ℝ) ^ c)) →
      D.GateTail (min (min a b) c / 2) := by
  sorry

/-- L8.1c assembled (08:76–123): for some `c' > 0`, the raw probability that a base gate fails at a key is at most
`e^{-n^{c'}}` for large `n`. -/
theorem gate_tail (hη₀ : 0 < η₀) (hβ₀ : 0 < β) (hβτ : β < tau8 η₀ / 4) (hp : 0 < p) (hK : 0 < K) :
    ∃ c' > (0 : ℝ), ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N),
      Std D γ K X Y R → GridFacts η₀ D.n → D.GateTail c' := by
  obtain ⟨nF, hF⟩ := filter_step η₀ β hη₀ hβ₀ hβτ
  obtain ⟨n₁', h34⟩ := gate34_tail η₀ γ β p K h hη₀ hβ₀ hβτ hK
  obtain ⟨c, hc, n₂, h2⟩ := gate2_tail η₀ γ β p K h hη₀ hp hK
  obtain ⟨n₃, hU⟩ := gate_tail_of η₀ β p h (tau8 η₀ / 2) (eta8 η₀ / 2) c
    (by linarith [tau8_pos hη₀]) (by linarith [eta8_pos hη₀]) hc
  set n₁ := max nF n₁' with hn₁def
  refine ⟨min (min (tau8 η₀ / 2) (eta8 η₀ / 2)) c / 2, ?_, max (max n₁ n₂) n₃, ?_⟩
  · have h1 : 0 < tau8 η₀ / 2 := by linarith [tau8_pos hη₀]
    have h2' : 0 < eta8 η₀ / 2 := by linarith [eta8_pos hη₀]
    have : 0 < min (min (tau8 η₀ / 2) (eta8 η₀ / 2)) c := lt_min (lt_min h1 h2') hc
    linarith
  · intro D hn X Y R hS hG
    have hn₁ : n₁ ≤ D.n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnF : nF ≤ D.n := le_trans (le_max_left _ _) hn₁
    have hn₁' : n₁' ≤ D.n := le_trans (le_max_right _ _) hn₁
    have hn₂ : n₂ ≤ D.n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn₃ : n₃ ≤ D.n := le_trans (le_max_right _ _) hn
    exact hU D hn₃ (gate1_tail η₀ γ β p K h hη₀ hβ₀ D X Y R hS)
      (h34 D hn₁' X Y R hS hG (hF D.n hnF)) (h2 D hn₂ X Y R hS)

/-! ## L8.1e: the fixed-presentation reference experiment (08:139–176) -/

/-- L8.1e(i) (08:144–154): on the candidate's gates, `S_g ≤ e^{hn^β + n^{τ/2}} Λ d^- / (.8A_g)` (G1, G2) and the
internal reference is `Λ d^- / ∫d^- dΛ` with `∫ d^- dΛ ≤ 1.1A_g` (G3), giving density `≤ e^{hn^β + n^{τ/2} + 1}`;
at `u ∈ E(g)`, `S_u(i)U_{u,i}(x) ≤ η_u(i)μ_i(x)1[x hits Θ_w, w ∈ E(u) ∪ {u}]/((1-Δ)Z_u)` since
`d_i^- / d_i^+ ≤ (1-Δ)^{-1}`, and the cross normalizer is at most `1.1 · 2^h A_u` (G4 at `u` omitting `g`), giving
density `≤ 2^{h+2}` (`Δ ≤ e^{-1}` for `n ≥ 1`). -/
theorem density_bounds (hp : 0 < p) (D : Ctx η₀ β p h) (hn : 1 ≤ D.n) : D.DensityBounds := by
  sorry

/-- L8.1e(ii) (08:162–163, 179–180): `Mden` does not read `Θ_g`; on the gate the true hypothetical data weight at
`Θ[g ↦ ξ]` is `F_ξ Q` (densities bounded, so no reference vanishes where data has mass), hence
`E_ξ q_{g,k} = Σ_o Q(o) M(o) 1[M(o) < ε₀] ≤ ε₀` (Lemma 3.7, first assertion). -/
theorem den_tail (D : Ctx η₀ β p h) (hd : D.DensityBounds) : D.DenTail := by
  sorry

/-- L8.1e(iii) (08:163–169): `N^h R'(ξ) ≤ e^{hn^β}` (width of `ν_i`), `F_ξ ≤ e^{T(hn^β + n^{τ/2} + 1)} 2^{2s(h+2)}`
(density bounds, `|E(g)| ≤ 2s`), and `M ≥ ε₀`; since `T = n^{τ/8 + o(1)}` and `β < τ/4`, the log density is at most
`1.5δhs log n` for large `n`. -/
theorem post_cap (hη₀ : 0 < η₀) (hβ₀ : 0 < β) (hβτ : β < tau8 η₀ / 4) (hh : 1 ≤ h) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      GridFacts η₀ D.n → D.DensityBounds → D.PostCap := by
  sorry

/-- L8.1e(iv) (08:171–176): a candidate with `F_ξ ≠ 0` passes its gates, so `Z_u > 0` and every observed cross tag
passes the cutoffs at `u` (`d^+ ≥ (1-Δ)e^{-n^{2τ}} > 0`), so `U_{u,i}` is the conditioned law and the observed
cross anchor hits `Θ_g = ξ` (as `g ∈ E(u)`); likewise each observed internal tag passes the cutoffs at `g`. -/
theorem f_support (D : Ctx η₀ β p h) (hn : 1 ≤ D.n) : D.FSupport := by
  sorry

end Nodes

end HypercubeRamsey.S08
