import HypercubeRamsey.S06.OddLoads
import HypercubeRamsey.S06.EvenRows_q_s06_even
import HypercubeRamsey.Tools.CubeGeometry
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.S06.Lane_q_s06_ev_d

open Classical
open OAI.HypercubeRamsey

/-! Geometry used by the separated even-row estimates. -/

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}

noncomputable def oddStar (v : CubeVertex n) : Finset (CubeVertex n) :=
  Finset.univ.filter fun u => ¬ IsEvenRole u ∧ (cube n).Adj v u

theorem residualDist_le_hammingDist (X : Ctx6 γ p₀ K n N E G M) (v w : CubeVertex n) :
    X.g.L.residualDist v w ≤ _root_.hammingDist v w := by
  unfold ChunkLayout6.residualDist _root_.hammingDist
  apply Finset.card_le_card
  intro a ha
  rcases Finset.mem_filter.mp ha with ⟨_, hd⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩

theorem oddStar_card_le (X : Ctx6 γ p₀ K n N E G M) (v : CubeVertex n) (hn : 0 < n) :
    (oddStar (n := n) v).card ≤ n := by
  let adj : Finset (CubeVertex n) := Finset.univ.filter fun u => (cube n).Adj v u
  have hsub : oddStar (n := n) v ⊆ adj := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.2⟩
  calc
    (oddStar (n := n) v).card ≤ adj.card := Finset.card_le_card hsub
    _ ≤ n := Lane_q_s06_even.adjacent_card_le_dimension_even v hn

theorem oddStar_disjoint_of_residualDist (X : Ctx6 γ p₀ K n N E G M)
    (v w : CubeVertex n) (hvw : 2 < X.g.L.residualDist v w) :
    Disjoint (oddStar (n := n) v) (oddStar (n := n) w) := by
  rw [Finset.disjoint_left]
  intro u huv huw
  have hadj₁ : (cube n).Adj v u := (Finset.mem_filter.mp huv).2.2
  have hadj₂ : (cube n).Adj w u := (Finset.mem_filter.mp huw).2.2
  have hdist₁ : _root_.hammingDist v u = 1 := hadj₁
  have hdist₂ : _root_.hammingDist w u = 1 := hadj₂
  have hdist₂' : _root_.hammingDist u w = 1 := by
    rw [_root_.hammingDist_comm u w]
    exact hdist₂
  have htri := _root_.hammingDist_triangle v u w
  have hdist : _root_.hammingDist v w ≤ 2 := by omega
  have := residualDist_le_hammingDist X v w
  omega

theorem expect_le_of_atomBound {Ω α : Type*} [Fintype Ω] [Fintype α] [DecidableEq α]
    (P : FinProb Ω) (f : Ω → α) (g q : α → ℝ)
    (hg : ∀ a, 0 ≤ g a)
    (hAtom : ∀ a, P.pr (fun ω => f ω = a) ≤ q a) :
    P.expect (fun ω => g (f ω)) ≤ ∑ a, q a * g a := by
  classical
  have hmass (a : α) : (FinProb.map P f).w a = P.pr (fun ω => f ω = a) := by
    unfold FinProb.map FinProb.pr
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : f ω = a <;> simp [h]
  calc
    P.expect (fun ω => g (f ω)) = (FinProb.map P f).expect g :=
      (FinProb.map_expect P f g).symm
    _ = ∑ a, (FinProb.map P f).w a * g a := rfl
    _ ≤ ∑ a, q a * g a := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_right _ (hg a)
      rw [hmass]
      exact hAtom a

end HypercubeRamsey.S06.Lane_q_s06_ev_d
