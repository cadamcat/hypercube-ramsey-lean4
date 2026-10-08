import HypercubeRamsey.S03.Height.Scale
import HypercubeRamsey.S03.Height.Selection_p_height_small
import HypercubeRamsey.S03.Height.Selection_p_height_main
import HypercubeRamsey.S03.Height.Split_opus_height
import OAI.Combinatorics.Ramsey.Hypercube

/-!
# L3.8: local height-selection subnodes and exported assembly

The probabilistic and geometric estimates are exposed as separate blueprint nodes. The exported theorem below
is intentionally only an assembly of those nodes; this keeps the parameter `n` abstract for Sections 9 and 14.
-/

namespace HypercubeRamsey

open scoped BigOperators
open OAI.HypercubeRamsey

/--
L3.8f (part 1): global good heights. The finite auxiliary law and eligibility selector make the
position-averaged supremum explicit, and the event is intersected with legality rather than conditioned on it.
-/
theorem height_selection_global (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) (reg : HDRegime b₀ b D) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
      p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
      c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      ∀ (Sites : p.Sites) {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
        (Esel : (p.Loc → Bool) → Aux → p.EligMap),
        ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
            ¬ p.GoodHeights Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2)) ≤
          Real.exp (-(p.n : ℝ) ^ (1 + c)) := by
  exact Lane_opus_height.height_selection_global_proof J₀ b₀ b σ ζ θ a c_d C_d D hp reg

/--
L3.8g (part 2): positive long height at a fixed query, also with one forced-present prospective center.
Legality is tested on the entire consultation domain and is intersected with the failure event.
-/
theorem height_selection_positive (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) (reg : HDRegime b₀ b D) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
      p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
      c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      ∀ (Sites : p.Sites) (v : CubeVertex p.d) (_hv : v ∈ Sites) (forced : Option p.Loc)
        {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
        (Esel : (p.Loc → Bool) → Aux → p.EligMap),
        (((p.posLawForced forced).prod πAux).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) (p.domBall Sites v p.Rlong) ∧
            0 < p.height Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) p.Rlong v) ≤
          Real.exp (-(p.n : ℝ) ^ c) := by
  exact Lane_opus_height.height_selection_positive_proof J₀ b₀ b σ ζ θ a c_d C_d D hp reg

/--
L3.8h (part 3): the long and short path maxima agree except with the stated stretched-exponential error.
The short radius is `D * floor(sqrt(m))`, where `m = ceil(n^α)`.
-/
theorem height_selection_short (J₀ b₀ b σ ζ θ a c_d C_d α : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) (reg : HDRegime b₀ b D)
    (hθ : 0.9 < θ) (hα : 0 < α ∧ α < 2 * (1 - ζ)) :
    ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
      p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
      c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      ∀ (Sites : p.Sites) (v : CubeVertex p.d) (_hv : v ∈ Sites) (forced : Option p.Loc)
        {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
        (Esel : (p.Loc → Bool) → Aux → p.EligMap),
        let m := ⌈(p.n : ℝ) ^ α⌉₊
        (((p.posLawForced forced).prod πAux).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) (p.domBall Sites v p.Rlong) ∧
            p.height Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) p.Rlong v ≠
              p.height Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) (p.Rshort m) v) ≤
          Real.exp (-3 * (m : ℝ) ^ ((1 : ℝ) / 5)) := by
  sorry

/-- L3.8i (part 4): a fixed eligible ID is selected at level zero with probability at most `3/λ`. -/
theorem height_selection_tie (p : HDParams) (hlam : 0 < p.lam) (P : p.Loc → Bool) (E : p.EligMap)
    (Sites : p.Sites) (v : CubeVertex p.d) (ℓ₀ : p.Loc)
    (hlegal : p.LegalAt P E v ⟨0, by omega⟩) (hℓ : ℓ₀ ∈ E v ⟨0, by omega⟩) :
    (p.actLaw.prod p.tieLaw).pr (fun ω =>
      p.height Sites P ω.1 E p.Rlong v = 0 ∧
        p.selection Sites P ω.1 E ω.2 v = some ℓ₀) ≤ 3 / p.lam := by
  exact height_selection_tie_p_height_small p hlam P E Sites v ℓ₀ hlegal hℓ

/--
L3.8j: uniform position-count concentration for all queried balls and levels. The geometric size assumptions
are explicit because the ball has volume `V` only when its radius does not exceed the cube dimension.
-/
theorem height_position_counts (p : HDParams) (Sites : p.Sites)
    (hlam : 0 < p.lam) (hV : 0 < p.V) (hr : p.r ≤ p.d)
    (hprob : p.lam / (p.V : ℝ) ≤ 1) :
    p.posLaw.pr (fun P => ∃ v ∈ Sites, ∃ j : Fin (p.H + 1),
      let count := (Finset.univ.filter (fun u : CubeVertex p.d =>
        P (u, j) = true ∧ _root_.hammingDist u v ≤ p.r)).card
      ((count : ℝ) < p.lam / 2 ∨ 2 * p.lam < (count : ℝ))) ≤
        2 * (Sites.card : ℝ) * ((p.H + 1 : ℕ) : ℝ) * Real.exp (-p.lam / 12) := by
  exact height_position_counts_p_height_small p Sites hlam hV hr hprob

/--
L3.8 (parts 1–4). This abstract-parameter form is the consumer-facing result: every probabilistic claim is
given by its blueprint subnode, and this theorem only assembles those claims.
-/
theorem height_selection (J₀ b₀ b σ ζ θ a c_d C_d α : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) (reg : HDRegime b₀ b D)
    (hθ : 0.9 < θ) (hα : 0 < α ∧ α < 2 * (1 - ζ)) :
    (∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
      p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
      c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      ∀ (Sites : p.Sites) {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
        (Esel : (p.Loc → Bool) → Aux → p.EligMap),
        ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
            ¬ p.GoodHeights Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2)) ≤
          Real.exp (-(p.n : ℝ) ^ (1 + c))) ∧
    (∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
      p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
      c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      ∀ (Sites : p.Sites) (v : CubeVertex p.d) (_hv : v ∈ Sites) (forced : Option p.Loc)
        {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
        (Esel : (p.Loc → Bool) → Aux → p.EligMap),
        (((p.posLawForced forced).prod πAux).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) (p.domBall Sites v p.Rlong) ∧
            0 < p.height Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) p.Rlong v) ≤
          Real.exp (-(p.n : ℝ) ^ c)) ∧
    (∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
      p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
      c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      ∀ (Sites : p.Sites) (v : CubeVertex p.d) (_hv : v ∈ Sites) (forced : Option p.Loc)
        {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
        (Esel : (p.Loc → Bool) → Aux → p.EligMap),
        let m := ⌈(p.n : ℝ) ^ α⌉₊
        (((p.posLawForced forced).prod πAux).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) (p.domBall Sites v p.Rlong) ∧
            p.height Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) p.Rlong v ≠
            p.height Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) (p.Rshort m) v) ≤
          Real.exp (-3 * (m : ℝ) ^ ((1 : ℝ) / 5))) ∧
    (∀ (p : HDParams) (_hlam : 0 < p.lam) (P : p.Loc → Bool) (E : p.EligMap) (Sites : p.Sites)
      (v : CubeVertex p.d) (ℓ₀ : p.Loc),
      p.LegalAt P E v ⟨0, by omega⟩ → ℓ₀ ∈ E v ⟨0, by omega⟩ →
      (p.actLaw.prod p.tieLaw).pr (fun ω =>
        p.height Sites P ω.1 E p.Rlong v = 0 ∧
          p.selection Sites P ω.1 E ω.2 v = some ℓ₀) ≤ 3 / p.lam) := by
  exact ⟨height_selection_global J₀ b₀ b σ ζ θ a c_d C_d D hp reg,
    height_selection_positive J₀ b₀ b σ ζ θ a c_d C_d D hp reg,
    height_selection_short J₀ b₀ b σ ζ θ a c_d C_d α D hp reg hθ hα,
    fun p hlam P E Sites v ℓ₀ hlegal hℓ =>
      height_selection_tie p hlam P E Sites v ℓ₀ hlegal hℓ⟩

end HypercubeRamsey
