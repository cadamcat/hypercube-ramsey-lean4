import HypercubeRamsey.S08.L81.HiddenNodes
import HypercubeRamsey.S08.L81.SelectionNodes_q_s08_sel

/-!
# Lemma 8.1, Step 5: hidden-history conditioning and local selection

Source: `sections/08-…tex`, lines 178–225 (L8.1f).
-/

noncomputable section

namespace HypercubeRamsey.S08

open HypercubeRamsey.Lane_q_s08_sel
open Classical OAI.HypercubeRamsey
open scoped BigOperators

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

/-- L8.1f(ii) (08:179–189): the hidden event at `g` reads the tuples in `B_grid(g, 2)` (gates at `g` and its
neighbours, the centre and anchor laws there, the references); two events meet only within grid distance four, at
most `(2s+1)^4` of them; by the gate tail and Markov on `E_{Θ_g} q_{g,k} ≤ ε₀` (independence of `Θ_g`),
`q_H ≤ e^{-n^{c'}} + (T+1)ε₀^{1/2} ≤ e^{-n^{c_H}}`, and `x_H = 2q_H` satisfies `q_H ≤ x_H(1-x_H)^{(2s+1)^4}`. -/
theorem hidden_lll (c' : ℝ) (hc' : 0 < c') (hη₀ : 0 < η₀) (hh : 1 ≤ h) :
    ∃ cH > (0 : ℝ), ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n →
      D.GateTail c' → D.DenTail → D.HiddenLLL (2 * Real.exp (-(D.n : ℝ) ^ cH)) := by
  sorry

/-- L8.1f(iii) (08:196–199): on incident ball counts at most `2λ`, the internal IDs of a candidate list are chosen
from at most `(n+1)(H+1) 2λ ≤ n^{13}` IDs (`≤ T` of them) and each of the `≤ 2s` cross IDs from at most `(H+1)2λ`,
so there are at most `exp(25(s+T) log n)` candidate lists; the constant does not depend on `h`. -/
theorem list_count (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.ListCount := by
  sorry

/-- L8.1f(iv) (08:208–212): a family has fewer than `n` lists of at most `T + 2s` IDs; an even site has at most
`(n - m + 1) + 2s` incident odd cells; so at most `n(n+1+2s)(T+2s) = o(λ)` IDs are forbidden at a site-level, and
at least `λ/2 - o(λ) ≥ λ/3` present IDs remain eligible. -/
theorem legal_of_counts (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.LegalOfCounts := by
  sorry

/-- L8.1f(v) (08:130–131, 212–214): on selection success, good heights select at every site (`¬ Bad` at the
selected level gives an active eligible ID); the ordinary neighbours of an odd cell lie within distance `D = 2`, so
their heights take at most two values and the crowd bound at one site per level gives at most `2n^b ≤ T` distinct
internal IDs; the realized list is a candidate list all of whose IDs are eligible where they are used, so it is
not bad (otherwise it meets a family list, whose IDs are forbidden there); legality follows from
`LegalOfCounts`. -/
theorem sel_conseq (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.LegalOfCounts → D.SelConseq := by
  sorry

/-- L8.1f(vi) (08:216–225): the selection at `(t, b)` consults eligibility in slice `t` at sites within `4H`
(the long rule), whose forbidden IDs come from the families at incident odd cells (keys within one of `t`), whose
lists read positions and tags of IDs within `r + 2` of those sites in slices within one of those keys, and `q_L`
reads hidden tuples within two of those keys; activations and ties are read only in slice `t`. -/
theorem sel_local (D : Ctx η₀ β p h) : D.SelLocal := by
  intro q q' e hΘ hLoc hAT
  let E := D.elig q.1.1 q.1.2 q.2.1.1 e.1
  let E' := D.elig q'.1.1 q'.1.2 q'.2.1.1 e.1
  unfold Ctx.sel
  apply selection_eq_of_local_data (hdP η₀ D.n) Finset.univ
    (q.1.2 e.1) (q'.1.2 e.1) (q.2.1.2 e.1) (q'.2.1.2 e.1)
    E E' (q.2.2 e.1) (q'.2.2 e.1) e.2 (Finset.mem_univ _)
  · intro v hv hdist
    have hsite : _root_.hammingDist v e.2 ≤ 4 * HH η₀ D.n := by
      simpa [HDParams.Rlong, hdP] using hdist
    have hp : ∀ k ∈ keyBall e.1 2, ∀ ℓ : D.Loc,
        _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 →
          q.1.2 k ℓ = q'.1.2 k ℓ := by
      intro k hk ℓ hℓ
      exact (hLoc k hk ℓ hℓ).1
    have ht : ∀ k ∈ keyBall e.1 2, ∀ ℓ : D.Loc,
        _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 →
          q.2.1.1 k ℓ = q'.2.1.1 k ℓ := by
      intro k hk ℓ hℓ
      exact (hLoc k hk ℓ hℓ).2
    have hE := elig_eq_of_local_inputs D q.1.1 q'.1.1 q.1.2 q'.1.2
      q.2.1.1 q'.2.1.1 e.1 v e.2 hsite hΘ hp ht
    funext j
    exact hE j
  · intro v hv j ℓ hℓ
    change ℓ ∈ D.elig q.1.1 q.1.2 q.2.1.1 e.1 v j at hℓ
    simp only [Ctx.elig, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    rcases hℓ with ⟨_, _, hdist, _⟩
    exact hdist
  · intro ℓ hℓ
    have hkey : e.1 ∈ keyBall e.1 2 := by
      simp only [keyBall, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [keyDist]
    have hbound : _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 := by
      have hbound' : _root_.hammingDist ℓ.1 e.2 ≤ 4 * HH η₀ D.n + rH D.n + 2 := by
        simpa [HDParams.Rlong, hdP] using hℓ
      omega
    exact (hLoc e.1 hkey ℓ hbound).1
  · intro ℓ hℓ
    have hbound : _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 := by
      have hbound' : _root_.hammingDist ℓ.1 e.2 ≤ 4 * HH η₀ D.n + rH D.n + 2 := by
        simpa [HDParams.Rlong, hdP] using hℓ
      omega
    exact (hAT ℓ hbound).1
  · intro j
    exact (hAT (e.2, j) (by simp)).2

/-- L8.1f(vii) (08:211): prospective ball counts lie in `[λ/2, 2λ]` everywhere except with probability at most
`(ℓ+1)^s · 2 · 2^{n-m} (H+1) e^{-λ/12} ≤ e^{-n}` (`height_position_counts` in every slice). -/
theorem pos_tail (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n →
      D.preLaw.pr (fun q => ¬ D.PosOK q.1.2) ≤ Real.exp (-(D.n : ℝ)) := by
  sorry

/-- L8.1f(viii) (08:191–195): the tags of a candidate list's distinct IDs are independent with laws `S_g`
(internal) and `S_u` (cross), so `E_t q_L = q_{g,k}` with `k ≤ T` internal IDs (`Mden` does not depend on how the
internal observations are indexed); at a hidden history avoiding the hidden events `q_{g,k} ≤ ε₀^{1/2}`, and
Markov gives `Pr(q_L > ε₀^{1/4}) ≤ ε₀^{1/4}`. -/
theorem bad_list_prob (D : Ctx η₀ β p h) : D.BadListProb := by
  sorry

/-- L8.1f(ix) (08:200–206): lists with disjoint ID sets have independent tags, so `n` disjoint bad lists at a cell
have probability at most `L_n^n ε₀^{n/4} = exp(n[25(s+T) - δhs/4] log n)` (`BadListProb`, `ListCount`), which for
`h ≥ 10⁸` beats the `exp(O(n + s log n))` cells. -/
theorem few_bad_tail (hη₀ : 0 < η₀) (hh : 10 ^ 8 ≤ h) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.ListCount → D.BadListProb →
      0 < D.rawHidden.pr (fun Θ => ∀ g, ¬ D.HBad Θ g) →
      D.preLaw.pr (fun q => D.PosOK q.1.2 ∧ ¬ D.FewBad q.1.1 q.1.2 q.2.1.1) ≤ Real.exp (-(D.n : ℝ)) := by
  sorry

/-- L8.1f(x) (08:214): eligibility in slice `g` is a function of the positions and of auxiliary randomness
independent of the activations of slice `g` (other slices' positions, tags); on legality (from `PosOK ∧ FewBad`)
Lemma 3.8 (`height_selection_global`, with `hd_admissible` and the linear regime) bounds the failure of good
heights in a slice by `e^{-n^{1+c}}`; a union over the `exp(O(s log n))` slices gives `e^{-n}`. -/
theorem height_tail (hη₀ : 0 < η₀)
    (hadm : HDAdmissible 10 (b0H η₀) (bH η₀) (sigmaH η₀) (zetaH η₀) (thetaH η₀) (aH η₀) (1 / 2) 1 2) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.LegalOfCounts →
      D.preLaw.pr (fun q => D.PosOK q.1.2 ∧ D.FewBad q.1.1 q.1.2 q.2.1.1 ∧
        ¬ D.GoodH q.1.1 q.1.2 q.2.1.1 q.2.1.2) ≤ Real.exp (-(D.n : ℝ)) := by
  sorry

end Nodes

end HypercubeRamsey.S08
