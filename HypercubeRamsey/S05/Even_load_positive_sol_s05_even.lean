import HypercubeRamsey.S05.Even_load_height_scales_sol_s05_even
import HypercubeRamsey.S05.Even_load_forced_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even
open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ}

theorem probability_unit_aux {A B : Type*} [Fintype A] [Fintype B]
    (P : FinProb A) (Q : FinProb B) (s : A → B → Prop) :
    ((P.prod (FinProb.uniformAll (Ω := PUnit) ⟨PUnit.unit⟩)).prod Q).pr
      (fun ω => s ω.1.1 ω.2) = (P.prod Q).pr (fun ω => s ω.1 ω.2) := by
  simp [FinProb.pr, FinProb.prod, FinProb.uniformAll, Fintype.sum_prod_type]

/-- The fixed Section 5 exponents permit one positive-height threshold before choosing any layer. -/
theorem eventual_positive_height (p : Params5 γ K' χ) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (X : Setup5 γ K' χ n N E G), X.p = p →
      ∀ (h : X.HeightChoice5) (Sites : h.hp.Sites) (v : CubeVertex h.hp.d), v ∈ Sites →
      ∀ (forced : Option h.hp.Loc) (Esel : (h.hp.Loc → Bool) → h.hp.EligMap),
        ((h.hp.posLawForced forced).prod h.hp.actLaw).pr (fun ω =>
          h.hp.Legal ω.1 (Esel ω.1) (h.hp.domBall Sites v h.hp.Rlong) ∧
            0 < h.hp.height Sites ω.1 ω.2 (Esel ω.1) h.hp.Rlong v) ≤ Real.exp (-(n : ℝ) ^ c) := by
  obtain ⟨c, hc, nH, hH⟩ := height_selection_positive 10 (p.alpha / 10000) (p.alpha / 2000)
    (p.alpha / 1000000) (p.alpha / 100000) (1 - p.alpha / 100000) (p.alpha / 20000)
    (1 / 2) 2 8 (canonicalHeightAdmissible p) (canonicalHeightRegime p)
  obtain ⟨nG, hG⟩ := Filter.eventually_atTop.mp (eventual_linear_height_geometry p)
  refine ⟨c, hc, max nH nG, ?_⟩
  intro n hn N E G X hp h Sites v hv forced Esel
  obtain ⟨hdlo, hdup, hreg⟩ := hG n ((le_max_right _ _).trans hn) N E G X hp h
  obtain ⟨hb0, hb, hσ, hζ, hθ, ha⟩ := h.fixed
  rw [hp] at hb0 hb hσ hζ hθ ha
  have htop : h.hp.H = topScale h.hp.n (p.alpha / 1000000) (p.alpha / 100000) := by
    change topScale n h.σ h.ζ = _
    rw [hσ, hζ]
    rfl
  have hbound := hH h.hp rfl htop rfl hb0 hb ((le_max_left _ _).trans hn)
    hdlo hdup hreg Sites v hv forced (FinProb.uniformAll (Ω := PUnit) ⟨PUnit.unit⟩) (fun P _ => Esel P)
  rw [probability_unit_aux (h.hp.posLawForced forced) h.hp.actLaw
    (fun P A => h.hp.Legal P (Esel P) (h.hp.domBall Sites v h.hp.Rlong) ∧
      0 < h.hp.height Sites P A (Esel P) h.hp.Rlong v)] at hbound
  exact hbound

end
end HypercubeRamsey.Lane_sol_s05_even
