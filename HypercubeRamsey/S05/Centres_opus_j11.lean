import HypercubeRamsey.S03.Height.Device

/-!
# J11 helpers: locality of the height-device selection (05:861–887)

The selection at a query `v` with consultation radius `R` reads the bad indicators of the site-levels
within `R` of `v` (through the reachable heights), and at `v` itself the eligible active IDs and the tie
permutations. These lemmas are stated for an abstract `HDParams` and abstract presence, activation,
eligibility and tie data, so that their kernel terms never unfold a concrete experiment.
-/

namespace HypercubeRamsey.Setup5.Lane_opus_s05_j11

open OAI.HypercubeRamsey

variable (p : HDParams)

/-- `Finset.filter_congr` for arbitrary decidability instances on both sides. -/
theorem filter_congr' {α : Type*} {P Q : α → Prop} {ip : DecidablePred P}
    {iq : DecidablePred Q} {s : Finset α} (h : ∀ x ∈ s, P x ↔ Q x) :
    @Finset.filter α P ip s = @Finset.filter α Q iq s := by
  let _ := ip
  let _ := iq
  exact Finset.filter_congr h

/-- A bad site-level depends on its eligible set, the activations of its eligible IDs, and the
presence and activations at its level within `r + D`. -/
theorem bad_congr (P A P' A' : p.Loc → Bool) (E E' : p.EligMap) (u : CubeVertex p.d)
    (j : Fin (p.H + 1)) (hE : E u j = E' u j) (hact : ∀ l ∈ E u j, A l = A' l)
    (hball : ∀ w : CubeVertex p.d, _root_.hammingDist w u ≤ p.r + p.D →
      P (w, j) = P' (w, j) ∧ A (w, j) = A' (w, j)) :
    p.Bad P A E u j ↔ p.Bad P' A' E' u j := by
  have h1 : (∀ l ∈ E u j, A l = false) ↔ (∀ l ∈ E' u j, A' l = false) := by
    rw [← hE]
    exact forall₂_congr fun l hl => by rw [hact l hl]
  have h2 : (Finset.univ.filter fun w : CubeVertex p.d =>
        P (w, j) = true ∧ A (w, j) = true ∧ _root_.hammingDist w u ≤ p.r + p.D) =
      (Finset.univ.filter fun w : CubeVertex p.d =>
        P' (w, j) = true ∧ A' (w, j) = true ∧ _root_.hammingDist w u ≤ p.r + p.D) := by
    apply filter_congr'
    intro w _
    constructor
    · rintro ⟨hp, ha, hd⟩
      obtain ⟨e1, e2⟩ := hball w hd
      exact ⟨e1 ▸ hp, e2 ▸ ha, hd⟩
    · rintro ⟨hp, ha, hd⟩
      obtain ⟨e1, e2⟩ := hball w hd
      exact ⟨e1 ▸ hp, e2 ▸ ha, hd⟩
  unfold HDParams.Bad
  rw [h1, h2]

/-- Every reachable site lies in the consultation ball. -/
theorem reach_dist {Sites : p.Sites} {P A : p.Loc → Bool} {E : p.EligMap} {vq : CubeVertex p.d}
    {R : ℕ} {u : CubeVertex p.d} {k : ℕ} (h : p.Reach Sites P A E vq R u k) :
    _root_.hammingDist u vq ≤ R := by
  induction h with
  | start v _ hd => exact hd
  | up v j _ _ _ ih => exact ih
  | down v v' j _ _ hdR _ _ => exact hdR

/-- Reachability transfers when badness transfers on the consultation ball. -/
theorem reach_of_bad_imp {Sites : p.Sites} {P A P' A' : p.Loc → Bool} {E E' : p.EligMap}
    {vq : CubeVertex p.d} {R : ℕ}
    (hbad : ∀ u : CubeVertex p.d, _root_.hammingDist u vq ≤ R → ∀ j : Fin (p.H + 1),
      p.Bad P A E u j → p.Bad P' A' E' u j)
    {u : CubeVertex p.d} {k : ℕ} (h : p.Reach Sites P A E vq R u k) :
    p.Reach Sites P' A' E' vq R u k := by
  induction h with
  | start v hv hd => exact HDParams.Reach.start v hv hd
  | up v j hj hr hb ih =>
      obtain ⟨hj', hb'⟩ := hb
      exact HDParams.Reach.up v j hj ih ⟨hj', hbad v (reach_dist p hr) _ hb'⟩
  | down v v' j _ hv' hdR hdD ih => exact HDParams.Reach.down v v' j ih hv' hdR hdD

open Classical in
/-- The height at a query depends only on badness within the consultation ball. -/
theorem height_congr (Sites : p.Sites) (P A P' A' : p.Loc → Bool) (E E' : p.EligMap)
    (R : ℕ) (vq : CubeVertex p.d)
    (hbad : ∀ u : CubeVertex p.d, _root_.hammingDist u vq ≤ R → ∀ j : Fin (p.H + 1),
      (p.Bad P A E u j ↔ p.Bad P' A' E' u j)) :
    p.height Sites P A E R vq = p.height Sites P' A' E' R vq := by
  have hfil : ((Finset.range (p.H + 1)).filter
        (fun j => p.Reach Sites P A E vq R vq j)) =
      ((Finset.range (p.H + 1)).filter
        (fun j => p.Reach Sites P' A' E' vq R vq j)) :=
    filter_congr' fun j _ =>
      ⟨reach_of_bad_imp p (fun u hu j => (hbad u hu j).mp),
        reach_of_bad_imp p (fun u hu j => (hbad u hu j).mpr)⟩
  unfold HDParams.height
  exact congrArg (fun s : Finset ℕ => s.sup id) hfil

open Classical in
/-- The selection rule as a function of the height, the bad indicators, the active eligible sets and
the priorities at the query. -/
noncomputable def selCore (h : ℕ) (bad : Fin (p.H + 1) → Prop)
    (active : Fin (p.H + 1) → Finset p.Loc)
    (prio : Fin (p.H + 1) → p.Loc → Fin (Fintype.card p.Loc)) : Option p.Loc := by
  if hj : h < p.H then
    let j' : Fin (p.H + 1) := ⟨h, by omega⟩
    if hbad : bad j' then
      exact none
    else
      let priorities := (active j').image (fun ℓ => prio j' ℓ)
      if hne : priorities.Nonempty then
        let q := priorities.min' hne
        have hq : q ∈ priorities := Finset.min'_mem priorities hne
        let hmem : ∃ ℓ, ℓ ∈ active j' ∧ prio j' ℓ = q :=
          Finset.mem_image.mp hq
        exact some (Classical.choose hmem)
      else
        exact none
  else
    exact none

theorem selectionAt_eq_selCore (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap)
    (τ : p.Ties) (R : ℕ) (v : CubeVertex p.d) :
    p.selectionAt Sites P A E τ R v =
      selCore p (p.height Sites P A E R v) (fun j => p.Bad P A E v j)
        (fun j => (E v j).filter (fun ℓ => A ℓ = true)) (fun j ℓ => p.priority τ (v, j) ℓ) :=
  rfl

/-- Locality of the selection rule: it reads badness within the consultation ball, and at the query
the eligible sets, the activations of eligible IDs and the tie permutations. -/
theorem selectionAt_congr (Sites : p.Sites) (P A P' A' : p.Loc → Bool) (E E' : p.EligMap)
    (τ τ' : p.Ties) (R : ℕ) (v : CubeVertex p.d)
    (hbad : ∀ u : CubeVertex p.d, _root_.hammingDist u v ≤ R → ∀ j : Fin (p.H + 1),
      (p.Bad P A E u j ↔ p.Bad P' A' E' u j))
    (hE : ∀ j, E v j = E' v j) (hact : ∀ j, ∀ l ∈ E v j, A l = A' l)
    (hτ : ∀ j, τ (v, j) = τ' (v, j)) :
    p.selectionAt Sites P A E τ R v = p.selectionAt Sites P' A' E' τ' R v := by
  have hv : _root_.hammingDist v v ≤ R := by simp
  have h1 := height_congr p Sites P A P' A' E E' R v hbad
  have h2 : (fun j => p.Bad P A E v j) = (fun j => p.Bad P' A' E' v j) :=
    funext fun j => propext (hbad v hv j)
  have h3 : (fun j => (E v j).filter (fun ℓ => A ℓ = true)) =
      (fun j => (E' v j).filter (fun ℓ => A' ℓ = true)) := by
    funext j
    rw [← hE j]
    exact Finset.filter_congr fun l hl => by rw [hact j l hl]
  have h4 : (fun j ℓ => p.priority τ (v, j) ℓ) = (fun j ℓ => p.priority τ' (v, j) ℓ) := by
    funext j ℓ
    unfold HDParams.priority
    rw [hτ j]
  rw [selectionAt_eq_selCore, selectionAt_eq_selCore, h1, h2, h3, h4]

theorem selCore_mem (h : ℕ) (bad : Fin (p.H + 1) → Prop) (active : Fin (p.H + 1) → Finset p.Loc)
    (prio : Fin (p.H + 1) → p.Loc → Fin (Fintype.card p.Loc)) (l : p.Loc)
    (hs : selCore p h bad active prio = some l) : ∃ j, l ∈ active j := by
  simp only [selCore] at hs
  split_ifs at hs with hj hbad hne
  have hmem := Finset.mem_image.mp (Finset.min'_mem _ hne)
  refine ⟨⟨h, by omega⟩, ?_⟩
  rw [← Option.some.inj hs]
  exact (Classical.choose_spec hmem).1

/-- A selected ID is an eligible ID at the query. -/
theorem selectionAt_mem (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap)
    (τ : p.Ties) (R : ℕ) (v : CubeVertex p.d) (l : p.Loc)
    (hs : p.selectionAt Sites P A E τ R v = some l) : ∃ j, l ∈ E v j := by
  rw [selectionAt_eq_selCore] at hs
  obtain ⟨j, hj⟩ := selCore_mem p _ _ _ _ l hs
  exact ⟨j, (Finset.mem_filter.mp hj).1⟩

end HypercubeRamsey.Setup5.Lane_opus_s05_j11
