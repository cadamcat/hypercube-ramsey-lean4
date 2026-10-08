import HypercubeRamsey.S05.Even_load_positive_sol_s05_even
import HypercubeRamsey.S05.Even_load_empirical_sol_s05_even
import HypercubeRamsey.S05.Even_load_volume_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

theorem pi_expect_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)] (P : ∀ i, FinProb (A i)) (i : I) (f : A i → ℝ) :
    (FinProb.pi P).expect (fun ω => f (ω i)) = (P i).expect f := by
  have hh := pi_expect_update P i (fun ω => f (ω i))
  simp only [Function.update_same] at hh
  rw [expect_constant] at hh
  exact hh.symm

theorem probability_as_indicator {A : Type*} [Fintype A] (P : FinProb A) (s : A → Prop) :
    P.pr s = P.expect (fun a => if s a then (1 : ℝ) else 0) := by
  unfold FinProb.pr FinProb.expect
  apply Finset.sum_congr rfl
  intro a _
  by_cases hs : s a <;> simp [hs]

theorem three_axes_probability {A B T : Type*} [Fintype A] [Fintype B] [Fintype T]
    (P : FinProb A) (Q : FinProb B) (R : FinProb T) (s : A → B → T → Prop) :
    (P.prod (Q.prod R)).pr (fun ω => s ω.1 ω.2.1 ω.2.2) =
      P.expect (fun a => Q.expect (fun b => R.expect (fun t => if s a b t then (1 : ℝ) else 0))) := by
  rw [prod_probability_expect P (Q.prod R) (fun a bt => s a bt.1 bt.2)]
  congr 1
  funext a
  rw [prod_probability_expect Q R (fun b t => s a b t)]
  simp_rw [probability_as_indicator]

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

def legallySelected (L : X.CentreLayer5) (H : X.KeyHist) (v : EvenRole5 n) (l : L.ht.hp.Loc)
    (ω : X.CΩ L.ht) : Prop :=
  L.ht.hp.Legal (Setup5.pos ω) (L.elig H ω)
      (L.ht.hp.domBall (X.sites L.ht) (X.siteOf v) L.ht.hp.Rlong) ∧
    X.selLong (L.elig H) ω v = some l

theorem array_statistic_mean (h : X.HeightChoice5) (H : X.KeyHist) (l : h.hp.Loc)
    (K : X.Ty) (x : Fin N) (hB : 0 < X.p.typeBlocks n K) (hS : 0 < X.p.typeSegs n K) :
    (centreArrayLaw X h H).expect (fun B => arrayEmpirical X K (B l K) x) = X.avgMarg H K x := by
  unfold centreArrayLaw
  rw [pi_expect_coordinate _ l (fun B => arrayEmpirical X K (B K) x)]
  rw [pi_expect_coordinate _ K (fun a => arrayEmpirical X K a x)]
  exact arrayEmpirical_mean X H K x hB hS

theorem fixed_arrays_selection_bound (L : X.CentreLayer5) (H : X.KeyHist) (v : EvenRole5 n)
    (l : L.ht.hp.Loc) (B : CentreArrays X L.ht) (hn : 0 < n) (ε : ℝ)
    (hpositive : ∀ Esel : (L.ht.hp.Loc → Bool) → L.ht.hp.EligMap,
      ((L.ht.hp.posLawForced (some l)).prod L.ht.hp.actLaw).pr (fun ω =>
        L.ht.hp.Legal ω.1 (Esel ω.1) (L.ht.hp.domBall (X.sites L.ht) (X.siteOf v) L.ht.hp.Rlong) ∧
          0 < L.ht.hp.height (X.sites L.ht) ω.1 ω.2 (Esel ω.1) L.ht.hp.Rlong (X.siteOf v)) ≤ ε) :
    L.ht.hp.posLaw.expect (fun P => L.ht.hp.actLaw.expect (fun A => L.ht.hp.tieLaw.expect (fun T =>
      if legallySelected X L H v l (centreFromAxes X P A T B) then (1 : ℝ) else 0))) ≤
        max 0 (min (L.ht.hp.lam / (L.ht.hp.V : ℝ)) 1) * (if l.2.val = 0 then 3 / L.ht.hp.lam else ε) := by
  let Esel := fun P => centreAxesElig X L H P B
  have hv : X.siteOf v ∈ X.sites L.ht := Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  have hlam : 0 < L.ht.hp.lam := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  have hshape (P : L.ht.hp.Loc → Bool) (j : Fin (L.ht.hp.H + 1)) (l : L.ht.hp.Loc)
      (hl : l ∈ Esel P (X.siteOf v) j) :
      P l = true ∧ l.2 = j ∧ _root_.hammingDist l.1 (X.siteOf v) ≤ L.ht.hp.r :=
    L.elig_shape H (centreFromAxes X P (fun _ => false) (fun _ => 1) B) (X.siteOf v) j l hl
  have heq (P) (A) (T) :
      legallySelected X L H v l (centreFromAxes X P A T B) ↔
        L.ht.hp.Legal P (Esel P) (L.ht.hp.domBall (X.sites L.ht) (X.siteOf v) L.ht.hp.Rlong) ∧
          L.ht.hp.selection (X.sites L.ht) P A (Esel P) T (X.siteOf v) = some l := by
    unfold legallySelected Setup5.selLong
    rw [elig_from_axes]
    rfl
  simp_rw [heq]
  rw [← three_axes_probability L.ht.hp.posLaw L.ht.hp.actLaw L.ht.hp.tieLaw
    (fun P A T => L.ht.hp.Legal P (Esel P) (L.ht.hp.domBall (X.sites L.ht) (X.siteOf v) L.ht.hp.Rlong) ∧
      L.ht.hp.selection (X.sites L.ht) P A (Esel P) T (X.siteOf v) = some l)]
  by_cases hl : l.2.val = 0
  · rw [if_pos hl]
    exact raw_zero_level_selection L.ht.hp hlam Esel (X.sites L.ht) (X.siteOf v) hv l hl hshape
  · rw [if_neg hl]
    exact raw_positive_level_selection L.ht.hp Esel (X.sites L.ht) (X.siteOf v) l (by omega) hshape ε (hpositive Esel)

theorem selected_array_mean (L : X.CentreLayer5) (H : X.KeyHist) (v : EvenRole5 n)
    (l : L.ht.hp.Loc) (x : Fin N) (hn : 0 < n) (ε : ℝ)
    (hB : 0 < X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1))
    (hS : 0 < X.p.typeSegs n (X.g.evenType (X.p.J n) v.1))
    (hpositive : ∀ Esel : (L.ht.hp.Loc → Bool) → L.ht.hp.EligMap,
      ((L.ht.hp.posLawForced (some l)).prod L.ht.hp.actLaw).pr (fun ω =>
        L.ht.hp.Legal ω.1 (Esel ω.1) (L.ht.hp.domBall (X.sites L.ht) (X.siteOf v) L.ht.hp.Rlong) ∧
          0 < L.ht.hp.height (X.sites L.ht) ω.1 ω.2 (Esel ω.1) L.ht.hp.Rlong (X.siteOf v)) ≤ ε) :
    (X.centreLaw L.ht H).expect (fun ω => if legallySelected X L H v l ω then
      arrayEmpirical X (X.g.evenType (X.p.J n) v.1) (Setup5.arr ω l (X.g.evenType (X.p.J n) v.1)) x else 0) ≤
      (max 0 (min (L.ht.hp.lam / (L.ht.hp.V : ℝ)) 1) * (if l.2.val = 0 then 3 / L.ht.hp.lam else ε)) *
        X.avgMarg H (X.g.evenType (X.p.J n) v.1) x := by
  have hh := centre_selected_array_mean X L H (legallySelected X L H v l)
    (fun B => arrayEmpirical X (X.g.evenType (X.p.J n) v.1) (B l (X.g.evenType (X.p.J n) v.1)) x)
    (fun B => arrayEmpirical_nonneg X _ _ _) _
    (fun B => fixed_arrays_selection_bound X L H v l B hn ε hpositive)
  rw [array_statistic_mean X L.ht H l _ x hB hS] at hh
  exact hh

end
end HypercubeRamsey.Lane_sol_s05_even
