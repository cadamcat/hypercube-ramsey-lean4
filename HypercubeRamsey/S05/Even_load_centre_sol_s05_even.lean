import HypercubeRamsey.S05.Even_load_axes_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

abbrev CentreArrays (h : X.HeightChoice5) := ∀ _l : h.hp.Loc, ∀ K : X.Ty, X.Array K

def centreFromAxes {h : X.HeightChoice5} (P A : h.hp.Loc → Bool) (T : h.hp.Ties)
    (B : CentreArrays X h) : X.CΩ h := fun l => (P l, A l, T l, B l)

def centreArrayLaw (h : X.HeightChoice5) (H : X.KeyHist) : FinProb (CentreArrays X h) :=
  FinProb.pi fun _l : h.hp.Loc => FinProb.pi fun K : X.Ty =>
    FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K

theorem centre_axes_expect (h : X.HeightChoice5) (H : X.KeyHist) (f : X.CΩ h → ℝ) :
    (X.centreLaw h H).expect f = h.hp.posLaw.expect (fun P => h.hp.actLaw.expect (fun A =>
      h.hp.tieLaw.expect (fun T => (centreArrayLaw X h H).expect (fun B => f (centreFromAxes X P A T B))))) := by
  unfold Setup5.centreLaw
  rw [pi_prod_expect]
  congr 1
  funext P
  rw [pi_prod_expect]
  congr 1
  funext A
  rw [pi_prod_expect]
  rfl

def centreAxesElig (L : X.CentreLayer5) (H : X.KeyHist) (P : L.ht.hp.Loc → Bool)
    (B : CentreArrays X L.ht) : L.ht.hp.EligMap :=
  L.elig H (centreFromAxes X P (fun _ => false) (fun _ => 1) B)

theorem elig_from_axes (L : X.CentreLayer5) (H : X.KeyHist) (P A : L.ht.hp.Loc → Bool)
    (T : L.ht.hp.Ties) (B : CentreArrays X L.ht) :
    L.elig H (centreFromAxes X P A T B) = centreAxesElig X L H P B := by
  apply L.elig_preActivation
  intro l
  exact ⟨rfl, rfl⟩

theorem expect_swap {A B : Type*} [Fintype A] [Fintype B] (P : FinProb A) (Q : FinProb B)
    (f : A → B → ℝ) : P.expect (fun a => Q.expect (f a)) = Q.expect (fun b => P.expect (fun a => f a b)) := by
  unfold FinProb.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expect_const_mul {A : Type*} [Fintype A] (P : FinProb A) (c : ℝ) (f : A → ℝ) :
    P.expect (fun a => c * f a) = c * P.expect f := by
  unfold FinProb.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem centre_arrays_first (h : X.HeightChoice5) (H : X.KeyHist) (f : X.CΩ h → ℝ) :
    (X.centreLaw h H).expect f = (centreArrayLaw X h H).expect (fun B =>
      h.hp.posLaw.expect (fun P => h.hp.actLaw.expect (fun A => h.hp.tieLaw.expect
        (fun T => f (centreFromAxes X P A T B))))) := by
  rw [centre_axes_expect]
  calc
    _ = h.hp.posLaw.expect (fun P => h.hp.actLaw.expect (fun A =>
        (centreArrayLaw X h H).expect (fun B => h.hp.tieLaw.expect (fun T => f (centreFromAxes X P A T B))))) := by
      congr 1
      funext P
      congr 1
      funext A
      exact expect_swap _ _ _
    _ = h.hp.posLaw.expect (fun P => (centreArrayLaw X h H).expect (fun B =>
        h.hp.actLaw.expect (fun A => h.hp.tieLaw.expect (fun T => f (centreFromAxes X P A T B))))) := by
      congr 1
      funext P
      exact expect_swap _ _ _
    _ = _ := expect_swap _ _ _

/-- A uniform selection bound at each fixed array configuration also bounds a nonnegative array statistic. -/
theorem centre_selected_array_mean (L : X.CentreLayer5) (H : X.KeyHist)
    (good : X.CΩ L.ht → Prop) (g : CentreArrays X L.ht → ℝ) (hg : ∀ B, 0 ≤ g B) (c : ℝ)
    (hbound : ∀ B, L.ht.hp.posLaw.expect (fun P => L.ht.hp.actLaw.expect (fun A =>
      L.ht.hp.tieLaw.expect (fun T => if good (centreFromAxes X P A T B) then (1 : ℝ) else 0))) ≤ c) :
    (X.centreLaw L.ht H).expect (fun ω => if good ω then g (fun l K => (ω l).2.2.2 K) else 0) ≤
      c * (centreArrayLaw X L.ht H).expect g := by
  rw [centre_arrays_first]
  have hpoint (B : CentreArrays X L.ht) :
      L.ht.hp.posLaw.expect (fun P => L.ht.hp.actLaw.expect (fun A =>
        L.ht.hp.tieLaw.expect (fun T => if good (centreFromAxes X P A T B) then g B else 0))) ≤ c * g B := by
    have heq (P) (A) (T) :
        (if good (centreFromAxes X P A T B) then g B else 0) =
          g B * (if good (centreFromAxes X P A T B) then (1 : ℝ) else 0) := by
      split_ifs <;> simp
    simp_rw [heq, expect_const_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbound B) (hg B)
  calc
    _ ≤ (centreArrayLaw X L.ht H).expect (fun B => c * g B) := by
      unfold FinProb.expect
      apply Finset.sum_le_sum
      intro B _
      exact mul_le_mul_of_nonneg_left (hpoint B) ((centreArrayLaw X L.ht H).nonneg B)
    _ = _ := expect_const_mul _ _ _

end
end HypercubeRamsey.Lane_sol_s05_even
