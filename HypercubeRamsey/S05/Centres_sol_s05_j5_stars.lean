import HypercubeRamsey.S05.Centres_sol_s05_j5
import HypercubeRamsey.S05.Centres_sol_s05_j5_scales

namespace HypercubeRamsey.Lane_sol_s05_j5

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)
variable {I : Type} [Fintype I] [DecidableEq I]

def candidates (Q : X.St.Site → ℕ → Finset I) (b : X.St.Site) (j : ℕ) : Finset I :=
  (X.St.neighbors b).biUnion fun t => Q t j ∪ Q t (j + 1)

def failureSets (H : X.KeyHist) (Q : X.St.Site → ℕ → Finset I) (A : X.ArraysOn I)
    (b : X.St.Site) (j : ℕ) : Finset (Finset I) :=
  ((Finset.univ : Finset (X.St.Site → I)).filter fun μ =>
    (∀ t ∈ X.St.neighbors b, μ t ∈ Q t j ∪ Q t (j + 1)) ∧
    ((X.St.neighbors b).image μ).card ≤ X.p.T n ∧
    ∃ y : OddRole5 n, X.St.stateOf y.1 = b ∧ X.step3FailOn H (starRecord X H A μ y) A).image
    fun μ => (X.St.neighbors b).image μ

theorem candidates_upper (Q : X.St.Site → ℕ → Finset I) (b : X.St.Site) (j : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hQ : ∀ t ∈ X.St.neighbors b, ∀ k, ((Q t k).card : ℝ) ≤ B) :
    ((candidates X Q b j).card : ℝ) ≤ 4 * n * B := by
  classical
  have hu : (candidates X Q b j).card ≤
      ∑ t ∈ X.St.neighbors b, (Q t j ∪ Q t (j + 1)).card := Finset.card_biUnion_le
  have hsum : (∑ t ∈ X.St.neighbors b, (Q t j ∪ Q t (j + 1)).card : ℕ) ≤
      ∑ t ∈ X.St.neighbors b, ((Q t j).card + (Q t (j + 1)).card) :=
    Finset.sum_le_sum fun t ht => Finset.card_union_le _ _
  have hr : ((candidates X Q b j).card : ℝ) ≤
      ∑ t ∈ X.St.neighbors b, (((Q t j).card : ℝ) + (Q t (j + 1)).card) := by
    exact_mod_cast hu.trans hsum
  have hb := Finset.sum_le_sum fun t ht => add_le_add (hQ t ht j) (hQ t ht (j + 1))
  have hdeg : ((X.St.neighbors b).card : ℝ) ≤ 2 * n := by exact_mod_cast X.St.degree_bound b
  have hdeg' := mul_le_mul_of_nonneg_right hdeg (by positivity : 0 ≤ B + B)
  have he := hr.trans hb
  simp only [Finset.sum_const, nsmul_eq_mul] at he
  nlinarith

theorem star_family_bound (H : X.KeyHist) (Q : X.St.Site → ℕ → Finset I)
    (y₀ : OddRole5 n) (j : ℕ) (cL cH C : ℝ)
    (hgood : X.KeyGood5 H cL cH) (hcount : X.RecordCount C)
    (hU : X.p.T n ≤ (candidates X Q (X.St.stateOf y₀.1) j).card) (hT : 0 < X.p.T n)
    (hbudget : ((candidates X Q (X.St.stateOf y₀.1) j).card : ℝ) ^ X.p.T n *
      Real.exp (C * ((X.p.T n : ℝ) * Real.log (X.p.T n) +
        (((X.g.roleKey (X.p.J n) y₀.1).level : ℝ) + 1) * Real.log (X.p.m n) +
        (if (X.g.roleKey (X.p.J n) y₀.1).isLeft ∧ (X.g.roleKey (X.p.J n) y₀.1).level = X.p.J n then
          (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0))) *
      X.step3Scale (if (X.g.roleKey (X.p.J n) y₀.1).isLeft then cL / 4 else cH / 6)
        (X.g.roleKey (X.p.J n) y₀.1) ≤ Real.exp (-4)) :
    (arrayLaw (I := I) X H).pr (fun A => n ≤ (Lane_sol_s05_centres.markingFamily
      (failureSets X H Q A (X.St.stateOf y₀.1) j)).card) ≤ Real.exp (-4) ^ n := by
  classical
  let U := candidates X Q (X.St.stateOf y₀.1) j
  let ℓ := X.g.roleKey (X.p.J n) y₀.1
  let t := X.g.sign y₀.1
  let v := X.g.severity y₀.1
  have hlift : ∀ A S, S ∈ failureSets X H Q A (X.St.stateOf y₀.1) j →
      ∃ r : concreteRecords X U ℓ t v,
        (∀ c ∈ (liftRecord X r).2.1, c.1 ∈ S) ∧ X.step3FailOn H (liftRecord X r) A := by
    intro A S hS
    obtain ⟨μ, hμ, heq⟩ := Finset.mem_image.mp hS
    obtain ⟨hQ, hsize, y, hy, hfail⟩ := (Finset.mem_filter.mp hμ).2
    have hdata := X.St.state_determines y.1 y₀.1 hy
    have hSU : S ⊆ U := by
      intro i hi
      rw [← heq] at hi
      obtain ⟨s, hs, his⟩ := Finset.mem_image.mp hi
      subst i
      exact Finset.mem_biUnion.mpr ⟨s, hs, hQ s hs⟩
    have hscope : ∀ c ∈ (starRecord X H A μ y).2.1, c.1 ∈ S := by
      intro c hc
      rw [← heq]
      simpa only [hy] using starRecord_ids X H A μ y c hc
    exact record_lift X H A U S ℓ t v (starRecord X H A μ y) y μ
      (starRecord_from X H A μ y hfail) hdata.2.2.2.2.2.2 hdata.2.1 hdata.2.2.1
      hSU (by simpa only [← heq] using hsize) hU hT hscope hfail
  exact (marking_family_lift X H U ℓ t v n
    (fun A => failureSets X H Q A (X.St.stateOf y₀.1) j) hlift).trans
      (disjoint_records_bound X H cL cH C hgood hcount U ℓ t v n (Real.exp (-4))
        (Real.exp_pos _).le hbudget)

end
end HypercubeRamsey.Lane_sol_s05_j5
