import HypercubeRamsey.S04.CoreLemmas

/-!
# Locality and independence in the preparatory experiment

Source: `sections/04-…tex`, lines 345–348, 500–502, 536–539, 575–585; blueprint L4.1i–k ("separated rows use
disjoint local data").  Every rule consults only data within distance `O(r + H)`; functions of data located in
disjoint sets are independent under the preparatory law; one tuple can be resampled from its prior.  The separated
raw factorizations `odd_factor` and `even_factor` are proved from these nodes.
-/

namespace HypercubeRamsey.S04

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- Locality of eligibility (04:345–347): `elig v l` reads positions within `r` of `v` and the marks of the odd
neighbours of `v`, whose pools lie within `r + 2` of `v` and whose validity tests read the odd masks of those
neighbours and the tuples of IDs within `r + 2`. -/
theorem elig_local {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) : EligLocal M tag := by
  sorry

/-- Locality of the selection (04:345–347): the long height at `v` follows paths through sites within `R_long`
of `v`, testing site-levels whose eligibility (`EligLocal`) and crowd balls lie within `R_long + r + 2`; the tie
used is that of `v`'s site-level. -/
theorem sel_local {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (_he : EligLocal M tag) : SelLocal M tag := by
  sorry

/-- Locality of the odd kernels: `OddOK` and `oddDraw` at `u` read the selections of the neighbours of `u`
(`SelLocal`), the odd mask of `u` and the tuples of IDs within `r + 1` of `u`. -/
theorem odd_local {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (_hs : SelLocal M tag) : OddLocal M tag := by
  sorry

/-- Locality of the mean even rows: `evenMean ω a x` reads the selection at `a`, legality on `a`'s consultation
ball, the neighbouring odd kernels and sampling laws, the counts, the mask and prior of the selected reference, the
reference mixtures and the likelihood (each recomputation replaces one tuple located within `r` of `a`), all within
`locR = R_long + r + 4` of `a`. -/
theorem even_local {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (_he : EligLocal M tag) (_hs : SelLocal M tag)
    (_ho : OddLocal M tag) : EvenLocal M tag := by
  sorry

/-- Independence (04:189–190, 575–577): under `prepLaw` the coordinates located at different sites are independent
(positions, activations and ties are products over IDs; masks are products over pairs and odd roles; tuples are
independent given the masks), so functions local to disjoint location sets factor. -/
theorem prep_factor {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag) :
    PrepFactor M tag q q' := by
  sorry

/-- Resampling (04:365–367, 536–539): given its mask, `W_{c,κ}` has law `prior` and is independent of all other
coordinates, so replacing it by an independent draw from `prior` leaves the preparatory law unchanged. -/
theorem prep_resample {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag) :
    Resample M tag q q' := by
  sorry

theorem disjoint_balls {n : ℕ} {v w : CubeVertex n} {R : ℕ} (h : 2 * R < _root_.hammingDist v w) :
    Disjoint (ballV v R) (ballV w R) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  have h1 : _root_.hammingDist v z ≤ R := (Finset.mem_filter.mp hz).2
  have h2 : _root_.hammingDist w z ≤ R := (Finset.mem_filter.mp hz').2
  have h3 := _root_.hammingDist_triangle v z w
  rw [_root_.hammingDist_comm z w] at h3
  omega

/-- Separated odd products in the raw experiment factor (04:500–502). -/
theorem odd_factor {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag)
    (hPF : PrepFactor M tag q q') (hOL : OddLocal M tag) : OddFactor M tag q q' := by
  intro y m u hsep
  have hdisj : ∀ i j, i ≠ j → Disjoint (ballV (u i).1 ((hd β γ n).Rlong + radius β γ n + 3))
      (ballV (u j).1 ((hd β γ n).Rlong + radius β γ n + 3)) := by
    intro i j hij
    apply disjoint_balls
    have h1 : 2 * locR β γ n < _root_.hammingDist (u i).1 (u j).1 := hsep i j hij
    have h2 : locR β γ n = (hd β γ n).Rlong + radius β γ n + 4 := rfl
    omega
  have hloc : ∀ i, LocalTo M tag (ballV (u i).1 ((hd β γ n).Rlong + radius β γ n + 3))
      (fun ω => (N : ℝ) * oddRow M tag ω (u i) y) := by
    intro i ω ω' hA
    obtain ⟨hiff, hdraw⟩ := hOL (u i) ω ω' hA
    by_cases hO : OddOK M tag ω (u i)
    · have hO' : OddOK M tag ω' (u i) := hiff.mp hO
      simp only [oddRow, if_pos hO, if_pos hO', hdraw y]
    · have hO' : ¬ OddOK M tag ω' (u i) := fun h => hO (hiff.mpr h)
      simp only [oddRow, if_neg hO, if_neg hO']
  have h := hPF m _ _ hdisj hloc
  rw [h]
  apply le_of_eq
  apply Finset.prod_congr rfl
  intro i _
  exact FinProb.expect_smul _ _ _

/-- Separated even products in the raw experiment factor (04:575–585). -/
theorem even_factor {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (q : XProf M tag) (q' : YProf M tag)
    (hPF : PrepFactor M tag q q') (hEL : EvenLocal M tag) : EvenFactor M tag q q' := by
  intro x m a hsep
  have hdisj : ∀ i j, i ≠ j → Disjoint (ballV (a i).1 (locR β γ n)) (ballV (a j).1 (locR β γ n)) :=
    fun i j hij => disjoint_balls (hsep i j hij)
  have hloc : ∀ i, LocalTo M tag (ballV (a i).1 (locR β γ n))
      (fun ω => (N : ℝ) * evenMean M tag ω (a i) x) := by
    intro i ω ω' hA
    simp only [hEL (a i) x ω ω' hA]
  have h := hPF m _ _ hdisj hloc
  rw [h]
  apply le_of_eq
  apply Finset.prod_congr rfl
  intro i _
  exact FinProb.expect_smul _ _ _

end HypercubeRamsey.S04
