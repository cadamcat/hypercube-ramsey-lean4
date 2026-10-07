import HypercubeRamsey.S07.AnchorStage_q_s07_anchor

set_option maxHeartbeats 1000000

namespace HypercubeRamsey.S07

open Classical
open scoped BigOperators

theorem odd_raw_row_mean_nonneg_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (Q : Γ.Key → FinProb M.ι) (c : Γ.Cell) (y : Fin N) :
    0 ≤ rawRowMean Γ M Q c y := by
  classical
  unfold rawRowMean FinProb.expect
  apply Finset.sum_nonneg
  intro σ hσ
  apply mul_nonneg ((FinProb.pi Q).nonneg σ)
  apply Finset.sum_nonneg
  intro W hW
  apply mul_nonneg ((rawAnchors Γ M σ).nonneg W)
  dsimp [cellRow]
  split_ifs with hv
  · by_cases hm : 0 < filterMass E G (M.ν (σ c.1)) (cellLabels Γ W c)
    · exact (filt_probability_and_support E G (M.ν (σ c.1))
        (cellLabels Γ W c) hm).1 y
    · simp [filt, hm]
  · exact le_rfl

theorem odd_raw_row_mean_average_le_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ K : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (P : Profiles7 Γ M K) (hcounts : GeomCounts Γ) (y : Fin N) :
    (Fintype.card (OddRole n) : ℝ)⁻¹ *
      ∑ u : OddRole n, (N : ℝ) * rawRowMean Γ M P.Q (Γ.key u.1) y ≤ K := by
  classical
  let cardOdd : ℝ := Fintype.card (OddRole n)
  let invAux : ℝ := ((2 : ℝ) ^ q)⁻¹
  let hval : Γ.Cell → ℝ := fun c => (N : ℝ) * rawRowMean Γ M P.Q c y
  have hcardPos : 0 < cardOdd := by
    dsimp [cardOdd]
    rw [hcounts.odd_card]
    positivity
  have hauxPos : 0 < (2 : ℝ) ^ q := by positivity
  have hfiber :
      ∑ u : OddRole n, hval (Γ.key u.1) =
        ∑ c : Γ.Cell,
          ((Finset.univ.filter fun u : OddRole n => Γ.key u.1 = c).card : ℝ) * hval c := by
    have hfib := (Fintype.sum_fiberwise (fun u : OddRole n => Γ.key u.1)
      (fun u => hval (Γ.key u.1))).symm
    calc
      ∑ u : OddRole n, hval (Γ.key u.1) =
          ∑ c : Γ.Cell,
            ∑ u : {u : OddRole n // Γ.key u.1 = c}, hval (Γ.key u.1) := hfib
      _ = ∑ c : Γ.Cell,
            ((Finset.univ.filter fun u : OddRole n => Γ.key u.1 = c).card : ℝ) * hval c := by
        apply Fintype.sum_congr
        intro c
        let S : Finset (OddRole n) := Finset.univ.filter fun u => Γ.key u.1 = c
        let e : {u : OddRole n // Γ.key u.1 = c} ≃ ↥S := {
          toFun := fun u => ⟨u.1, by simp [S, u.2]⟩
          invFun := fun u => ⟨u.1, (Finset.mem_filter.mp u.2).2⟩
          left_inv := by intro u; apply Subtype.ext; rfl
          right_inv := by intro u; apply Subtype.ext; rfl
        }
        have hcard : Fintype.card {u : OddRole n // Γ.key u.1 = c} = S.card :=
          (Fintype.card_congr e).trans (Fintype.card_coe S)
        calc
          (∑ u : {u : OddRole n // Γ.key u.1 = c}, hval (Γ.key u.1)) =
              ∑ u : {u : OddRole n // Γ.key u.1 = c}, hval c := by
                apply Fintype.sum_congr
                intro u
                simp [u.property]
          _ = ((Finset.univ.filter fun u : OddRole n => Γ.key u.1 = c).card : ℝ) * hval c := by
                simp [S, hcard, Finset.sum_const]
  have hterm (g : Γ.Key) (t : Γ.AuxWord) :
      cardOdd⁻¹ *
          (cardOdd * invAux * Γ.keyMass g) *
            ((N : ℝ) * rawRowMean Γ M P.Q (g, t) y) =
        Γ.keyMass g * ((N : ℝ) *
          (invAux * rawRowMean Γ M P.Q (g, t) y)) := by
    field_simp [ne_of_gt hcardPos, ne_of_gt hauxPos]
  have hweighted :
      cardOdd⁻¹ *
          ∑ c : Γ.Cell,
            ((Finset.univ.filter fun u : OddRole n => Γ.key u.1 = c).card : ℝ) * hval c =
        ∑ g : Γ.Key, Γ.keyMass g *
          ((N : ℝ) * (invAux * ∑ t : Γ.AuxWord, rawRowMean Γ M P.Q (g, t) y)) := by
    calc
      cardOdd⁻¹ *
          ∑ c : Γ.Cell,
            ((Finset.univ.filter fun u : OddRole n => Γ.key u.1 = c).card : ℝ) * hval c =
        ∑ c : Γ.Cell, cardOdd⁻¹ *
          (((Finset.univ.filter fun u : OddRole n => Γ.key u.1 = c).card : ℝ) * hval c) := by
            rw [Finset.mul_sum]
      _ = ∑ g : Γ.Key, ∑ t : Γ.AuxWord,
          cardOdd⁻¹ * (cardOdd * invAux * Γ.keyMass g) *
            ((N : ℝ) * rawRowMean Γ M P.Q (g, t) y) := by
              rw [Fintype.sum_prod_type]
              apply Fintype.sum_congr
              intro g
              apply Fintype.sum_congr
              intro t
              rw [hcounts.odd_count (g, t)]
              change cardOdd⁻¹ *
                  ((cardOdd * invAux * Γ.keyMass g) *
                    ((N : ℝ) * rawRowMean Γ M P.Q (g, t) y)) =
                cardOdd⁻¹ * (cardOdd * invAux * Γ.keyMass g) *
                  ((N : ℝ) * rawRowMean Γ M P.Q (g, t) y)
              ring
      _ = ∑ g : Γ.Key, Γ.keyMass g *
          ((N : ℝ) * (invAux * ∑ t : Γ.AuxWord, rawRowMean Γ M P.Q (g, t) y)) := by
            apply Fintype.sum_congr
            intro g
            calc
              (∑ t : Γ.AuxWord,
                  cardOdd⁻¹ * (cardOdd * invAux * Γ.keyMass g) *
                    ((N : ℝ) * rawRowMean Γ M P.Q (g, t) y)) =
                ∑ t : Γ.AuxWord, Γ.keyMass g *
                  ((N : ℝ) * (invAux * rawRowMean Γ M P.Q (g, t) y)) := by
                    apply Fintype.sum_congr
                    intro t
                    exact hterm g t
              _ = Γ.keyMass g *
                  ((N : ℝ) * (invAux * ∑ t : Γ.AuxWord,
                    rawRowMean Γ M P.Q (g, t) y)) := by
                    calc
                      (∑ t : Γ.AuxWord, Γ.keyMass g *
                          ((N : ℝ) * (invAux * rawRowMean Γ M P.Q (g, t) y))) =
                        ∑ t : Γ.AuxWord,
                          (Γ.keyMass g * (N : ℝ) * invAux) *
                            rawRowMean Γ M P.Q (g, t) y := by
                              apply Fintype.sum_congr
                              intro t
                              ring
                      _ = (Γ.keyMass g * (N : ℝ) * invAux) *
                          ∑ t : Γ.AuxWord, rawRowMean Γ M P.Q (g, t) y := by
                            rw [← Finset.mul_sum]
                      _ = Γ.keyMass g *
                          ((N : ℝ) * (invAux * ∑ t : Γ.AuxWord,
                            rawRowMean Γ M P.Q (g, t) y)) := by ring
  have hkeyNonneg (g : Γ.Key) : 0 ≤ Γ.keyMass g := by
    unfold GridGeom.keyMass
    apply Finset.prod_nonneg
    intro r hr
    unfold GridGeom.binMass
    apply Finset.sum_nonneg
    intro k hk
    split_ifs
    · positivity
    · exact le_rfl
  have havg :
      ∑ g : Γ.Key, Γ.keyMass g *
          ((N : ℝ) * (invAux * ∑ t : Γ.AuxWord, rawRowMean Γ M P.Q (g, t) y)) ≤ K := by
    calc
      _ ≤ ∑ g : Γ.Key, Γ.keyMass g * K := by
        apply Finset.sum_le_sum
        intro g hg
        exact mul_le_mul_of_nonneg_left (P.row_mean g y) (hkeyNonneg g)
      _ = K := by
        rw [← Finset.sum_mul, hcounts.keyMass_sum]
        ring
  calc
    (Fintype.card (OddRole n) : ℝ)⁻¹ *
        ∑ u : OddRole n, (N : ℝ) * rawRowMean Γ M P.Q (Γ.key u.1) y =
      cardOdd⁻¹ * ∑ c : Γ.Cell,
        ((Finset.univ.filter fun u : OddRole n => Γ.key u.1 = c).card : ℝ) * hval c := by
          rw [show cardOdd = (Fintype.card (OddRole n) : ℝ) by rfl]
          rw [hfiber]
    _ = ∑ g : Γ.Key, Γ.keyMass g *
        ((N : ℝ) * (invAux * ∑ t : Γ.AuxWord, rawRowMean Γ M P.Q (g, t) y)) := hweighted
    _ ≤ K := havg

end HypercubeRamsey.S07
