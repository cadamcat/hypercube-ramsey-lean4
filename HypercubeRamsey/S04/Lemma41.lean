import HypercubeRamsey.S04.Defs
import HypercubeRamsey.S04.PlateauProof
import HypercubeRamsey.S04.StageProof
import HypercubeRamsey.S04.CoreAssembly

/-!
# Lemma 4.1: bias versus purity

The section-level export is the Part B consumed form. The density plateau and the one-index cube
construction are kept as separate blueprint nodes; the stage wrapper records their composition.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey
open scoped BigOperators

/-- Statement of L4.1a (frozen with its body). -/
def L4_1aStatement (β γ : ℝ) : Prop :=
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N (E : Fin N → Fin N → Prop)
      (A B : Finset (Fin N)) (q : Law N × Law N),
      PBias (pw β) (pw γ) (h4 β γ) n N E q.1 q.2 →
      q.1.SupportedIn A → q.2.SupportedIn B →
      ∃ G : Colour, ∃ μ ν : Law N,
        PrepLaw β γ G n N E μ ν ∧ μ.SupportedIn A ∧ ν.SupportedIn B

/-- L4.1a (04:29–81): a biased witness can be prepared inside the same residual supports. -/
theorem L4_1a (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    L4_1aStatement β γ := by
  exact l41a_proof β γ hβ hβγ hγ

/-- Statement of L4.1-core (frozen with its body). -/
def L4_1_coreStatement (β γ K : ℝ) : Prop :=
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n ≥ n₀, ∀ N,
      LargeHost C₀ n N → ∀ (E : Fin N → Fin N → Prop) (G : Colour)
      (X' Y' : Finset (Fin N)) {ι : Type} [Fintype ι]
      (ρ : FinProb ι) (μ ν : ι → Law N),
      (∀ i, PrepLaw β γ G n N E (μ i) (ν i)) →
      (∀ i, (μ i).SupportedIn X' ∧ (ν i).SupportedIn Y') →
      (∀ x, ∑ i, ρ.w i * (μ i).w x ≤ K / N) →
      (∀ y, ∑ i, ρ.w i * (ν i).w y ≤ K / N) →
      (∀ μ' ν' : Law N,
        μ'.WidthLE (2 * (n : ℝ) ^ β) → ν'.WidthLE (2 * (n : ℝ) ^ γ) →
        dens E G μ' ν' ≤ Real.exp (-(n : ℝ) ^ h4 β γ) →
        ¬ (μ'.SupportedIn X' ∧ ν'.SupportedIn Y')) →
      Nonempty ((OAI.HypercubeRamsey.cube n).Copy
        (OAI.HypercubeRamsey.crossGraph (Hits E G)))

/-- L4.1-core (04:89–598): balanced prepared patches force a cube unless a pair is nearly monochromatic.

The last hypothesis is the colour-`G` sparse-pair exclusion (`PureLaw β γ (h4 β γ) (!G)` in Part A).
The proof is the assembly `S04.l41_core_proof` of the Section 4 nodes (`S04/CoreAssembly.lean`).
-/
theorem L4_1_core (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1)
    (K : ℝ) (hK : 0 < K) :
    L4_1_coreStatement β γ K := by
  exact S04.l41_core_proof β γ hβ hβγ hγ K hK

/-- L4.1 (04:9–16): stage wrapper from the plateau and single-index core.

It includes the Part B monotonicity in `h'`: the proof fixes the exponent `h4 β γ` from the two
sub-nodes and transfers bias and purity along `0 < h' ≤ h4 β γ`.
-/
theorem L4_1_stage (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1)
    (_plateau : L4_1aStatement β γ)
    (_core : ∀ (K : ℝ) (hK : 0 < K), L4_1_coreStatement β γ K) :
    ∃ h > (0 : ℝ), ∀ h' : ℝ, 0 < h' → h' ≤ h → ∀ T : Stage,
      Available T (PBias (pw β) (pw γ) h').toPatch →
      EventuallyAbsent T (PPure β γ h').toPatch → False := by
  exact l41_stage_proof β γ hβ hβγ hγ _plateau _core

/-- L4.1, Part B consumed form (04:9–16; Part B §1.3).

The exported proof is an application of the stage wrapper, with its two Section 4 sub-nodes supplied
explicitly above.
-/
theorem L4_1 (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ h > (0 : ℝ), ∀ h' : ℝ, 0 < h' → h' ≤ h → ∀ T : Stage,
      Available T (PBias (pw β) (pw γ) h').toPatch →
      EventuallyAbsent T (PPure β γ h').toPatch → False := by
  exact L4_1_stage β γ hβ hβγ hγ
    (L4_1a β γ hβ hβγ hγ)
    (fun K hK => L4_1_core β γ hβ hβγ hγ K hK)

end HypercubeRamsey
