import HypercubeRamsey.S07.AnchorStage_q_s07_anchor_product

set_option maxHeartbeats 10000000

namespace HypercubeRamsey.S07

open Classical
open scoped BigOperators

private theorem pi_expect_equiv_q_s07_anchor
    {α β Ω : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype Ω]
    (e : α ≃ β) (P : α → FinProb Ω) (Q : β → FinProb Ω)
    (hP : ∀ a, P a = Q (e a)) (f : (β → Ω) → ℝ) :
    (FinProb.pi P).expect (fun a => f ((Equiv.piCongrLeft (fun _ : β => Ω) e) a)) =
      (FinProb.pi Q).expect f := by
  classical
  unfold FinProb.expect
  let ePi := Equiv.piCongrLeft (fun _ : β => Ω) e
  have hweight (a : α → Ω) : (FinProb.pi P).w a = (FinProb.pi Q).w (ePi a) := by
    simp only [FinProb.pi]
    calc
      (∏ x, (P x).w (a x)) = ∏ x, (Q (e x)).w (a x) := by simp [hP]
      _ = ∏ b, (Q b).w (a (e.symm b)) :=
        Fintype.prod_equiv e _ _ (by intro x; simp)
      _ = ∏ b, (Q b).w ((ePi a) b) := by
        apply Fintype.prod_congr
        intro b
        simp [ePi, Equiv.piCongrLeft]
  apply Fintype.sum_equiv ePi
  intro a
  rw [hweight a]

private theorem finprob_nonempty_invalid_q_s07_anchor {α : Type*} [Fintype α]
    (P : FinProb α) : Nonempty α := by
  classical
  by_contra h
  haveI : IsEmpty α := ⟨fun a => h ⟨a⟩⟩
  have hsum := P.sum_eq_one
  simp at hsum

private theorem pi_pr_eq_expect_indicator_q_s07_anchor
    {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A = P.expect (fun ω => if A ω then (1 : ℝ) else 0) := by
  classical
  unfold FinProb.pr FinProb.expect
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : A ω <;> simp [h]

private theorem pr_compl_q_s07_anchor
    {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr (fun x => ¬ A x) = 1 - P.pr A := by
  classical
  have hsum : P.pr A + P.pr (fun x => ¬ A x) = 1 := by
    unfold FinProb.pr
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x, ((if A x then P.w x else 0) +
        @ite ℝ (¬ A x) (Classical.propDecidable (¬ A x)) (P.w x) 0)) =
          ∑ x, P.w x := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases h : A x <;> simp [h]
      _ = 1 := P.sum_eq_one
  linarith

private theorem miss_probability_le_error_q_s07_anchor
    {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (μ : Law N)
    (y : Fin N) (ε : ℝ) (hdeg : 1 - ε ≤ colDeg E G μ y) :
    μ.pr (fun x => ¬ Hits E G x y) ≤ ε := by
  classical
  have hcolDeg : colDeg E G μ y = μ.pr (fun x => Hits E G x y) := by
    unfold colDeg FinProb.pr
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hh : Hits E G x y <;> simp [hh]
  have hsplit : colDeg E G μ y + μ.pr (fun x => ¬ Hits E G x y) = 1 := by
    rw [hcolDeg, pr_compl_q_s07_anchor μ (fun x => Hits E G x y)]
    ring
  linarith

private theorem pi_expect_coordinate_q_s07_anchor
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (P : ι → FinProb Ω) (i : ι) (f : Ω → ℝ) :
    (FinProb.pi P).expect (fun a => f (a i)) = (P i).expect f := by
  classical
  let s : Finset ι := {i}
  let I := {x : ι // x ∈ s}
  letI : Unique I := {
    default := ⟨i, by simp [s]⟩
    uniq := by
      intro x
      apply Subtype.ext
      exact Finset.mem_singleton.mp (by simpa [s] using x.2)
  }
  let e : (I → Ω) ≃ Ω := Equiv.piUnique (fun _ : I => Ω)
  have hdefault : (default : I).1 = i := by
    exact Finset.mem_singleton.mp (by simpa [s] using (default : I).property)
  have h := FinProb.pi_marginal_expect P s (fun a => f (e a))
  have hleft : (fun ω : ι → Ω => (fun a : I → Ω => f (e a)) (fun x => ω x.1)) =
      (fun ω => f (ω i)) := by
    funext ω
    simp [e, Equiv.piUnique, hdefault]
  have hright : (FinProb.pi (fun x : I => P x.1)).expect (fun a => f (e a)) =
      (P i).expect f := by
    unfold FinProb.expect
    apply Fintype.sum_equiv e
    intro a
    have hweight : (FinProb.pi (fun x : I => P x.1)).w a = (P i).w (e a) := by
      simp [FinProb.pi, e, Equiv.piUnique, hdefault]
    rw [hweight]
  calc
    (FinProb.pi P).expect (fun a => f (a i)) =
        (FinProb.pi P).expect (fun a : ι → Ω =>
          (fun a' : I → Ω => f (e a')) (fun x => a x.1)) := by
          rw [hleft]
    _ = (FinProb.pi (fun x : I => P x.1)).expect (fun a => f (e a)) := h
    _ = (P i).expect f := hright

private theorem passesAnchors_append_q_s07_anchor
    {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (L K : List (Fin N))
    (y : Fin N) :
    passesAnchors E G (L ++ K) y ↔
    passesAnchors E G L y ∧ passesAnchors E G K y := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x (List.mem_append.mpr (Or.inl hx))
    · intro x hx
      exact h x (List.mem_append.mpr (Or.inr hx))
  · rintro ⟨hL, hK⟩ x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hL x hx
    · exact hK x hx

private theorem filterMass_append_split_q_s07_anchor
    {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (ν : Law N)
    (L K : List (Fin N)) :
    filterMass E G ν L = filterMass E G ν (L ++ K) +
      ∑ y, if passesAnchors E G L y ∧ ¬ passesAnchors E G K y then ν.w y else 0 := by
  classical
  unfold filterMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [passesAnchors_append_q_s07_anchor]
  by_cases hL : passesAnchors E G L y <;>
    by_cases hK : passesAnchors E G K y <;> simp [hL, hK]

private theorem ownNames_nodup_q_s07_anchor
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)
    (g : Γ.Key) (t : Γ.AuxWord) : (Γ.ownNames g t).Nodup := by
  unfold GridGeom.ownNames GridGeom.ownWords
  apply List.Nodup.map
  · intro x y hxy
    exact congrArg Prod.snd hxy
  · exact Finset.nodup_toList _

private theorem ownNames_card_q_s07_anchor
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)
    (hloc : GeomLocal Γ) (g : Γ.Key) (t : Γ.AuxWord) :
    ((Γ.ownNames g t).toFinset.card : ℕ) = q + 1 := by
  rw [List.toFinset_card_of_nodup (ownNames_nodup_q_s07_anchor Γ g t)]
  simp [GridGeom.ownNames, GridGeom.ownWords, hloc.auxBall_one_card t]

private noncomputable def ownCrossMass_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (c : Γ.Cell) (W : Γ.Cell → Fin N) : ℝ :=
  filterMass E G (M.ν (σ c.1)) (crossLabels Γ W c)

private noncomputable def ownMissingMass_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (c : Γ.Cell) (W : Γ.Cell → Fin N) : ℝ :=
  ∑ y, if passesAnchors E G (crossLabels Γ W c) y ∧
      ¬ passesAnchors E G ((Γ.ownNames c.1 c.2).map W) y then
    (M.ν (σ c.1)).w y else 0

private noncomputable def ownLossFraction_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (c : Γ.Cell) (W : Γ.Cell → Fin N) : ℝ :=
  if 0 < ownCrossMass_q_s07_anchor Γ M σ c W then
    ownMissingMass_q_s07_anchor Γ M σ c W / ownCrossMass_q_s07_anchor Γ M σ c W
  else 0

private theorem ownMissing_le_anchor_losses_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (c : Γ.Cell) (W : Γ.Cell → Fin N) :
    ownMissingMass_q_s07_anchor Γ M σ c W ≤
      ∑ w ∈ (Γ.ownNames c.1 c.2).toFinset,
        ∑ y, if passesAnchors E G (crossLabels Γ W c) y ∧ ¬ Hits E G (W w) y then
          (M.ν (σ c.1)).w y else 0 := by
  classical
  let ν := M.ν (σ c.1)
  let L := Γ.ownNames c.1 c.2
  let S := L.toFinset
  unfold ownMissingMass_q_s07_anchor
  calc
    (∑ y, if passesAnchors E G (crossLabels Γ W c) y ∧
        ¬ passesAnchors E G (L.map W) y then ν.w y else 0) ≤
      ∑ y, ∑ w ∈ S, if passesAnchors E G (crossLabels Γ W c) y ∧
          ¬ Hits E G (W w) y then ν.w y else 0 := by
            apply Finset.sum_le_sum
            intro y hy
            by_cases hc : passesAnchors E G (crossLabels Γ W c) y
            · by_cases ho : passesAnchors E G (L.map W) y
              · have hnonneg : 0 ≤ ∑ w ∈ S,
                    if passesAnchors E G (crossLabels Γ W c) y ∧
                      ¬ Hits E G (W w) y then ν.w y else 0 := by
                  apply Finset.sum_nonneg
                  intro w hw
                  split_ifs <;> simp [ν.nonneg y]
                simpa [hc, ho] using hnonneg
              · have hex : ∃ w ∈ L, ¬ Hits E G (W w) y := by
                  unfold passesAnchors at ho
                  push_neg at ho
                  rcases ho with ⟨x, hx, hmiss⟩
                  rcases List.mem_map.mp hx with ⟨w, hw, hW⟩
                  exact ⟨w, hw, by simpa [hW] using hmiss⟩
                obtain ⟨w, hw, hmiss⟩ := hex
                have hwS : w ∈ S := List.mem_toFinset.mpr hw
                have hnonneg : ∀ z ∈ S,
                    0 ≤ if passesAnchors E G (crossLabels Γ W c) y ∧
                      ¬ Hits E G (W z) y then ν.w y else 0 := by
                  intro z hz
                  split_ifs <;> simp [ν.nonneg y]
                have hsingle := Finset.single_le_sum hnonneg hwS
                have hterm : (if passesAnchors E G (crossLabels Γ W c) y ∧
                    ¬ Hits E G (W w) y then ν.w y else 0) = ν.w y := by
                  simp [hc, hmiss]
                calc
                  (if passesAnchors E G (crossLabels Γ W c) y ∧
                      ¬ passesAnchors E G (L.map W) y then ν.w y else 0) = ν.w y := by
                        simp [hc, ho]
                  _ = (if passesAnchors E G (crossLabels Γ W c) y ∧
                      ¬ Hits E G (W w) y then ν.w y else 0) := hterm.symm
                  _ ≤ ∑ z ∈ S, if passesAnchors E G (crossLabels Γ W c) y ∧
                      ¬ Hits E G (W z) y then ν.w y else 0 := hsingle
            · simp [hc]
    _ = ∑ w ∈ S, ∑ y, if passesAnchors E G (crossLabels Γ W c) y ∧
          ¬ Hits E G (W w) y then ν.w y else 0 := by
            rw [Finset.sum_comm]

private theorem ownLossFraction_expect_bound_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hloc : GeomLocal Γ) (σ : Γ.Key → M.ι) (c : Γ.Cell) :
    (rawAnchors Γ M σ).expect (ownLossFraction_q_s07_anchor Γ M σ c) ≤
      ((q : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) := by
  classical
  let ν : Law N := M.ν (σ c.1)
  let μ : Law N := M.μ (σ c.1)
  let ε : ℝ := Real.exp (-(n : ℝ) ^ p)
  let crossL : List Γ.Cell := Γ.crossNames c.1 c.2
  let ownL : List Γ.Cell := Γ.ownNames c.1 c.2
  let ownSet : Finset Γ.Cell := ownL.toFinset
  let Pcell : Γ.Cell → FinProb (Fin N) := fun x => M.μ (σ x.1)
  let Own := {x : Γ.Cell // x ∈ ownSet}
  let Out := {x : Γ.Cell // x ∉ ownSet}
  let Pcoord : Own → FinProb (Fin N) := fun x => Pcell x.1
  let Pown : FinProb (Own → Fin N) := FinProb.pi Pcoord
  let Pout : FinProb (Out → Fin N) := FinProb.pi fun x : Out => Pcell x.1
  let ePi := Equiv.piEquivPiSubtypeProd (fun x : Γ.Cell => x ∈ ownSet) (fun _ => Fin N)
  have hownNodup : ownL.Nodup := by
    dsimp [ownL]
    exact ownNames_nodup_q_s07_anchor Γ c.1 c.2
  have hownCard : ownSet.card = q + 1 := by
    dsimp [ownSet, ownL]
    exact ownNames_card_q_s07_anchor Γ hloc c.1 c.2
  have hcrossOwnDisj : List.Disjoint crossL ownL := by
    have h := List.disjoint_of_nodup_append (hloc.fullNames_nodup c)
    simpa [crossL, ownL, GridGeom.fullNames, GridGeom.crossNames, GridGeom.ownNames] using h
  have hcrossNotOwn (x : Γ.Cell) (hx : x ∈ crossL) : x ∉ ownSet := by
    intro hmem
    exact (List.disjoint_left.mp hcrossOwnDisj hx) (List.mem_toFinset.mp hmem)
  have hownKey (x : Γ.Cell) (hx : x ∈ ownL) : x.1 = c.1 := by
    dsimp [ownL, GridGeom.ownNames] at hx
    rcases List.mem_map.mp hx with ⟨t, ht, heq⟩
    exact (congrArg Prod.fst heq).symm
  have hPownLaw (x : Own) : Pcoord x = μ := by
    change M.μ (σ x.1.1) = M.μ (σ c.1)
    rw [hownKey x.1 (List.mem_toFinset.mp x.2)]
  have hmiss (y : Fin N) (hy : 0 < ν.w y) :
      μ.pr (fun z => ¬ Hits E G z y) ≤ ε := by
    have h := miss_probability_le_error_q_s07_anchor E G (M.μ (σ c.1)) y ε
      ((M.pure (σ c.1)).2.2 y hy)
    simpa [μ, ε] using h
  have hcoordPr (x : Own) (y : Fin N) :
      Pown.expect (fun a => if ¬ Hits E G (a x) y then (1 : ℝ) else 0) =
        μ.pr (fun z => ¬ Hits E G z y) := by
    calc
      Pown.expect (fun a => if ¬ Hits E G (a x) y then (1 : ℝ) else 0) =
          (Pcoord x).expect (fun z => if ¬ Hits E G z y then (1 : ℝ) else 0) := by
            simpa [Pown] using
              (pi_expect_coordinate_q_s07_anchor Pcoord x
                (fun z => if ¬ Hits E G z y then (1 : ℝ) else 0))
      _ = μ.pr (fun z => ¬ Hits E G z y) := by
            rw [hPownLaw x]
            unfold FinProb.expect FinProb.pr
            apply Finset.sum_congr rfl
            intro z hz
            by_cases hmiss : ¬ Hits E G z y <;> simp [hmiss]
  have hfactor :
      (rawAnchors Γ M σ).expect (ownLossFraction_q_s07_anchor Γ M σ c) =
        Pout.expect (fun b => Pown.expect (fun a =>
          ownLossFraction_q_s07_anchor Γ M σ c (ePi.symm (a, b)))) := by
    have hsplit : (FinProb.pi Pcell).expect (ownLossFraction_q_s07_anchor Γ M σ c) =
        ∑ a : Own → Fin N, ∑ b : Out → Fin N,
          Pown.w a * Pout.w b *
            ownLossFraction_q_s07_anchor Γ M σ c (ePi.symm (a, b)) := by
      simpa [Pown, Pout] using
        (anchor_pi_expect_split Pcell ownSet (ownLossFraction_q_s07_anchor Γ M σ c))
    rw [show rawAnchors Γ M σ = FinProb.pi Pcell by rfl, hsplit]
    unfold FinProb.expect Pout Pown
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hfiber (b : Out → Fin N) :
      Pown.expect (fun a =>
        ownLossFraction_q_s07_anchor Γ M σ c (ePi.symm (a, b))) ≤
          ((q : ℝ) + 1) * ε := by
    let Wb : Γ.Cell → Fin N := fun x =>
      if hx : x ∈ ownSet then Classical.choice
        (finprob_nonempty_invalid_q_s07_anchor (M.μ (σ c.1)) ) else b ⟨x, hx⟩
    let Wab : (Own → Fin N) → (Out → Fin N) → Γ.Cell → Fin N :=
      fun a b => ePi.symm (a, b)
    let Cb : ℝ := ownCrossMass_q_s07_anchor Γ M σ c Wb
    let H : Γ.Cell → (Own → Fin N) → ℝ := fun x a =>
      if hx : x ∈ ownSet then
        ∑ y, if passesAnchors E G (crossLabels Γ Wb c) y ∧
          ¬ Hits E G (a ⟨x, hx⟩) y then ν.w y else 0
      else 0
    have hWcross (a : Own → Fin N) (x : Γ.Cell) (hx : x ∈ crossL) :
        Wab a b x = Wb x := by
      have hxOut : x ∉ ownSet := hcrossNotOwn x hx
      dsimp [Wab, Wb]
      simp [ePi, Equiv.piEquivPiSubtypeProd, hxOut]
    have hcrossLabels (a : Own → Fin N) :
        crossLabels Γ (Wab a b) c = crossLabels Γ Wb c := by
      unfold crossLabels
      apply List.map_congr_left
      intro x hx
      exact hWcross a x (by simpa [crossL] using hx)
    have hCeq (a : Own → Fin N) :
        ownCrossMass_q_s07_anchor Γ M σ c (Wab a b) = Cb := by
      change filterMass E G ν (crossLabels Γ (Wab a b) c) =
        filterMass E G ν (crossLabels Γ Wb c)
      rw [hcrossLabels a]
    have hHexpect (x : Γ.Cell) (hx : x ∈ ownSet) : Pown.expect (H x) ≤ ε * Cb := by
      have hterms (y : Fin N) :
          (∑ a, Pown.w a * (if passesAnchors E G (crossLabels Γ Wb c) y ∧
            ¬ Hits E G (a ⟨x, hx⟩) y then ν.w y else 0)) ≤
          (if passesAnchors E G (crossLabels Γ Wb c) y then ν.w y * ε else 0) := by
        by_cases hpass : passesAnchors E G (crossLabels Γ Wb c) y
        · by_cases hν : 0 < ν.w y
          · have hsum :
              (∑ a, Pown.w a * (if ¬ Hits E G (a ⟨x, hx⟩) y then ν.w y else 0)) =
                  ν.w y * Pown.expect (fun a =>
                    if ¬ Hits E G (a ⟨x, hx⟩) y then (1 : ℝ) else 0) := by
              calc
                _ = ∑ a, ν.w y * (Pown.w a *
                    (if ¬ Hits E G (a ⟨x, hx⟩) y then (1 : ℝ) else 0)) := by
                      apply Finset.sum_congr rfl
                      intro a ha
                      by_cases hm : ¬ Hits E G (a ⟨x, hx⟩) y <;> simp [hm, mul_assoc, mul_comm]
                _ = ν.w y * ∑ a, Pown.w a *
                    (if ¬ Hits E G (a ⟨x, hx⟩) y then (1 : ℝ) else 0) := by
                      rw [Finset.mul_sum]
                _ = _ := rfl
            have hmissBound := hmiss y hν
            calc
              (∑ a, Pown.w a * (if passesAnchors E G (crossLabels Γ Wb c) y ∧
                ¬ Hits E G (a ⟨x, hx⟩) y then ν.w y else 0)) =
                  ν.w y * Pown.expect (fun a =>
                    if ¬ Hits E G (a ⟨x, hx⟩) y then (1 : ℝ) else 0) := by
                      simpa [hpass] using hsum
              _ = ν.w y * μ.pr (fun z => ¬ Hits E G z y) := by
                    rw [hcoordPr ⟨x, hx⟩ y]
              _ ≤ ν.w y * ε := mul_le_mul_of_nonneg_left hmissBound (ν.nonneg y)
              _ = if passesAnchors E G (crossLabels Γ Wb c) y then
                    ν.w y * ε else 0 := by simp [hpass]
          · have hν0 : ν.w y = 0 := le_antisymm (le_of_not_gt hν) (ν.nonneg y)
            simp [hpass, hν0]
        · simp [hpass]
      calc
        Pown.expect (H x) =
            ∑ y, ∑ a, Pown.w a * (if passesAnchors E G (crossLabels Γ Wb c) y ∧
              ¬ Hits E G (a ⟨x, hx⟩) y then ν.w y else 0) := by
                unfold FinProb.expect H
                simp [hx]
                calc
                  (∑ a, Pown.w a * ∑ y, if passesAnchors E G (crossLabels Γ Wb c) y ∧
                      ¬ Hits E G (a ⟨x, hx⟩) y then ν.w y else 0) =
                    ∑ a, ∑ y, Pown.w a *
                      (if passesAnchors E G (crossLabels Γ Wb c) y ∧
                        ¬ Hits E G (a ⟨x, hx⟩) y then ν.w y else 0) := by
                          apply Finset.sum_congr rfl
                          intro a ha
                          rw [Finset.mul_sum]
                  _ = ∑ y, ∑ a, Pown.w a *
                      (if passesAnchors E G (crossLabels Γ Wb c) y ∧
                        ¬ Hits E G (a ⟨x, hx⟩) y then ν.w y else 0) := by
                          rw [Finset.sum_comm]
                  _ = ∑ y, ∑ a, if passesAnchors E G (crossLabels Γ Wb c) y ∧
                        ¬ Hits E G (a ⟨x, hx⟩) y then Pown.w a * ν.w y else 0 := by
                          apply Finset.sum_congr rfl
                          intro y hy
                          apply Finset.sum_congr rfl
                          intro a ha
                          by_cases h : passesAnchors E G (crossLabels Γ Wb c) y ∧
                            ¬ Hits E G (a ⟨x, hx⟩) y <;> simp [h]
        _ ≤ ∑ y, if passesAnchors E G (crossLabels Γ Wb c) y then
              ν.w y * ε else 0 := by
                apply Finset.sum_le_sum
                intro y hy
                exact hterms y
        _ = ε * Cb := by
              unfold Cb ownCrossMass_q_s07_anchor
              rw [show crossLabels Γ Wb c = crossL.map Wb by rfl]
              unfold filterMass
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y hy
              by_cases hp' : passesAnchors E G (crossLabels Γ Wb c) y <;>
                simp [hp', mul_comm, ν]
    have hmissing (a : Own → Fin N) :
        ownMissingMass_q_s07_anchor Γ M σ c (Wab a b) ≤ ∑ x ∈ ownSet, H x a := by
      have h := ownMissing_le_anchor_losses_q_s07_anchor Γ M σ c (Wab a b)
      calc
        ownMissingMass_q_s07_anchor Γ M σ c (Wab a b) ≤
            ∑ x ∈ ownSet, ∑ y, if passesAnchors E G
              (crossLabels Γ (Wab a b) c) y ∧ ¬ Hits E G (Wab a b x) y then ν.w y else 0 := h
        _ = ∑ x ∈ ownSet, H x a := by
              apply Finset.sum_congr rfl
              intro x hx
              have hEval : Wab a b x = a ⟨x, hx⟩ := by
                simp [Wab, ePi, Equiv.piEquivPiSubtypeProd, hx]
              simp [H, hx, hcrossLabels a, hEval, ν]
    by_cases hCb : 0 < Cb
    · have hPoint (a : Own → Fin N) :
          ownLossFraction_q_s07_anchor Γ M σ c (Wab a b) ≤
            (∑ x ∈ ownSet, H x a) / Cb := by
        rw [ownLossFraction_q_s07_anchor, if_pos (by simpa [hCeq a] using hCb)]
        rw [hCeq a]
        exact div_le_div_of_nonneg_right (hmissing a) hCb.le
      have hsumExpect :
          Pown.expect (fun a => (∑ x ∈ ownSet, H x a) / Cb) =
            ∑ x ∈ ownSet, (Pown.expect (H x)) / Cb := by
        unfold FinProb.expect
        calc
          (∑ a, Pown.w a * ((∑ x ∈ ownSet, H x a) / Cb)) =
              ∑ a, ∑ x ∈ ownSet, Pown.w a * (H x a / Cb) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [Finset.sum_div, Finset.mul_sum]
          _ = ∑ x ∈ ownSet, ∑ a, Pown.w a * (H x a / Cb) := by
                rw [Finset.sum_comm]
          _ = ∑ x ∈ ownSet, (∑ a, Pown.w a * H x a) / Cb := by
                apply Finset.sum_congr rfl
                intro x hx
                rw [Finset.sum_div]
                apply Finset.sum_congr rfl
                intro a ha
                ring
          _ = ∑ x ∈ ownSet, (Pown.expect (H x)) / Cb := rfl
      calc
        Pown.expect (fun a => ownLossFraction_q_s07_anchor Γ M σ c (Wab a b)) ≤
            Pown.expect (fun a => (∑ x ∈ ownSet, H x a) / Cb) :=
              FinProb.expect_mono Pown (fun a => hPoint a)
        _ = ∑ x ∈ ownSet, (Pown.expect (H x)) / Cb := hsumExpect
        _ ≤ ∑ x ∈ ownSet, ε := by
              apply Finset.sum_le_sum
              intro x hx
              apply (div_le_iff₀ hCb).2
              exact hHexpect x hx
        _ = ((q : ℝ) + 1) * ε := by
              simp [hownCard, nsmul_eq_mul]
    · have hzero (a : Own → Fin N) :
          ownLossFraction_q_s07_anchor Γ M σ c (Wab a b) = 0 := by
        rw [ownLossFraction_q_s07_anchor, if_neg (by simpa [hCeq a] using hCb)]
      have hexpzero : Pown.expect (fun a =>
          ownLossFraction_q_s07_anchor Γ M σ c (Wab a b)) = 0 := by
        unfold FinProb.expect
        simp [hzero]
      rw [hexpzero]
      positivity
  calc
    (rawAnchors Γ M σ).expect (ownLossFraction_q_s07_anchor Γ M σ c) =
        Pout.expect (fun b => Pown.expect (fun a =>
          ownLossFraction_q_s07_anchor Γ M σ c (ePi.symm (a, b)))) := hfactor
    _ ≤ Pout.expect (fun _ => ((q : ℝ) + 1) * ε) :=
          FinProb.expect_mono Pout (fun b => hfiber b)
    _ = ((q : ℝ) + 1) * ε := FinProb.expect_const Pout _
    _ = ((q : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) := by rfl

theorem ownFail_pr_bound_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hn : 1 ≤ n)
    (hloc : GeomLocal Γ) (σ : Γ.Key → M.ι) (c : Γ.Cell) :
    (rawAnchors Γ M σ).pr (fun W => ¬ OwnValid Γ M (σ c.1) W c) ≤
      (n : ℝ) ^ 2 * ((q : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) := by
  classical
  let ν : Law N := M.ν (σ c.1)
  let t : ℝ := (n : ℝ) ^ (-2 : ℝ)
  let C : (Γ.Cell → Fin N) → ℝ := ownCrossMass_q_s07_anchor Γ M σ c
  let F : (Γ.Cell → Fin N) → ℝ := fun W =>
    filterMass E G ν (cellLabels Γ W c)
  let L : (Γ.Cell → Fin N) → ℝ := ownMissingMass_q_s07_anchor Γ M σ c
  let r : (Γ.Cell → Fin N) → ℝ := ownLossFraction_q_s07_anchor Γ M σ c
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnreal
  have htpos : 0 < t := by dsimp [t]; exact Real.rpow_pos_of_pos hnpos _
  have hfilter_nonneg (L' : List (Fin N)) :
      0 ≤ filterMass E G ν L' := by
    unfold filterMass
    apply Finset.sum_nonneg
    intro y hy
    split_ifs <;> simp [ν.nonneg y]
  have hdecomp (W : Γ.Cell → Fin N) : C W = F W + L W := by
    simpa [C, F, L, ν, ownCrossMass_q_s07_anchor, ownMissingMass_q_s07_anchor,
      crossLabels, cellLabels, GridGeom.fullNames, GridGeom.crossNames,
      GridGeom.ownNames, List.map_append] using
      (filterMass_append_split_q_s07_anchor E G ν (crossLabels Γ W c)
        ((Γ.ownNames c.1 c.2).map W))
  have hbad_ratio (W : Γ.Cell → Fin N)
      (hbad : ¬ OwnValid Γ M (σ c.1) W c) : t < r W := by
    have hCnonneg : 0 ≤ C W := by
      exact hfilter_nonneg (crossLabels Γ W c)
    have hFnonneg : 0 ≤ F W := by
      exact hfilter_nonneg (cellLabels Γ W c)
    have hlt : F W < (1 - (n : ℝ) ^ (-2 : ℝ)) * C W := by
      have hlt' := lt_of_not_ge hbad
      simpa [F, C, ν, ownCrossMass_q_s07_anchor] using hlt'
    by_cases hCzero : C W = 0
    · have hv : OwnValid Γ M (σ c.1) W c := by
        unfold OwnValid
        have hCzero' : filterMass E G ν (crossLabels Γ W c) = 0 := by
          simpa [C, ν, ownCrossMass_q_s07_anchor] using hCzero
        rw [hCzero']
        simpa using hFnonneg
      exact (hbad hv).elim
    · have hCpos : 0 < C W := lt_of_le_of_ne hCnonneg (Ne.symm hCzero)
      have hLost : t * C W < L W := by
        change (n : ℝ) ^ (-2 : ℝ) * C W < L W
        nlinarith [hlt, hdecomp W]
      change t < if 0 < C W then L W / C W else 0
      rw [if_pos hCpos]
      exact (lt_div_iff₀ hCpos).2 hLost
  have hrnonneg (W : Γ.Cell → Fin N) : 0 ≤ r W := by
    unfold r ownLossFraction_q_s07_anchor
    split_ifs with hC
    · apply div_nonneg
      · unfold ownMissingMass_q_s07_anchor
        apply Finset.sum_nonneg
        intro y hy
        split_ifs with hmiss
        · exact (M.ν (σ c.1)).nonneg y
        · exact le_rfl
      · exact hC.le
    · exact le_rfl
  have hsub : (rawAnchors Γ M σ).pr
      (fun W => ¬ OwnValid Γ M (σ c.1) W c) ≤
      (rawAnchors Γ M σ).pr (fun W => t ≤ r W) := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro W hW
    by_cases hbad : ¬ OwnValid Γ M (σ c.1) W c
    · have hlt := hbad_ratio W hbad
      simp [hbad, le_of_lt hlt]
    · simp [hbad]
      split_ifs
      · exact (rawAnchors Γ M σ).nonneg W
      · rfl
  have hmark := FinProb.markov (rawAnchors Γ M σ) r t hrnonneg htpos
  have hexpect := ownLossFraction_expect_bound_q_s07_anchor Γ M hloc σ c
  have hpowInv : t⁻¹ = (n : ℝ) ^ 2 := by
    dsimp [t]
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    simp
  calc
    (rawAnchors Γ M σ).pr (fun W => ¬ OwnValid Γ M (σ c.1) W c) ≤
        (rawAnchors Γ M σ).pr (fun W => t ≤ r W) := hsub
    _ ≤ (rawAnchors Γ M σ).expect r / t := hmark
    _ ≤ (((q : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p)) / t :=
      div_le_div_of_nonneg_right (by simpa [r] using hexpect) htpos.le
    _ = (n : ℝ) ^ 2 * ((q : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) := by
      rw [div_eq_mul_inv, hpowInv]
      ring

theorem crossFail_pr_eq_key_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (c : Γ.Cell) :
    (rawAnchors Γ M σ).pr
        (fun W => ¬ CrossValidRow Γ M (σ c.1) (fun h => W (h, c.2)) c.1) =
      crossFailKey Γ M σ c.1 := by
  classical
  let S : Finset Γ.Cell := Finset.univ.filter fun w => w.2 = c.2
  let Pcell : Γ.Cell → FinProb (Fin N) := fun w => M.μ (σ w.1)
  let Pkey : Γ.Key → FinProb (Fin N) := fun g => M.μ (σ g)
  let index (g : Γ.Key) : {w : Γ.Cell // w ∈ S} :=
    ⟨(g, c.2), by simp [S]⟩
  let eKey : {w : Γ.Cell // w ∈ S} ≃ Γ.Key := {
    toFun := fun w => w.1.1
    invFun := fun g => index g
    left_inv := by
      intro w
      apply Subtype.ext
      rcases w with ⟨⟨g, t⟩, hw⟩
      have ht : t = c.2 := by simpa [S] using hw
      subst t
      rfl
    right_inv := by intro g; rfl
  }
  let ePi := Equiv.piCongrLeft (fun _ : Γ.Key => Fin N) eKey
  let badCell (W : Γ.Cell → Fin N) : Prop :=
    ¬ CrossValidRow Γ M (σ c.1) (fun h => W (h, c.2)) c.1
  let badKey (a : Γ.Key → Fin N) : Prop :=
    ¬ CrossValidRow Γ M (σ c.1) a c.1
  let fcell : (∀ w : {w : Γ.Cell // w ∈ S}, Fin N) → ℝ := fun a =>
    if ¬ CrossValidRow Γ M (σ c.1) (fun h => a (index h)) c.1 then (1 : ℝ) else 0
  have hdep : FinProb.DependsOn (fun W => if badCell W then (1 : ℝ) else 0) S := by
    intro W W' hW
    have heq : (fun h => W (h, c.2)) = fun h => W' (h, c.2) := by
      funext h
      exact hW (h, c.2) (by simp [S])
    simp [badCell, heq]
  have hRawExpect :
      (rawAnchors Γ M σ).expect (fun W => if badCell W then (1 : ℝ) else 0) =
        (FinProb.pi (fun w : {w : Γ.Cell // w ∈ S} => Pcell w.1)).expect fcell := by
    let W₀ : Γ.Cell → Fin N := Classical.choice
      (finprob_nonempty_invalid_q_s07_anchor (rawAnchors Γ M σ))
    have hproj (a : ∀ w : {w : Γ.Cell // w ∈ S}, Fin N) :
        (fun h => (glue S W₀ a) (h, c.2)) = fun h => a (index h) := by
      funext h
      simp [glue, index, S]
    have h := pi_glue_expect_eq_q_s07_anchor Pcell S
      (fun W => if badCell W then (1 : ℝ) else 0) W₀ hdep W₀
    calc
      (rawAnchors Γ M σ).expect (fun W => if badCell W then (1 : ℝ) else 0) =
          (FinProb.pi Pcell).expect (fun W => if badCell W then (1 : ℝ) else 0) := by rfl
      _ = (FinProb.pi (fun w : {w : Γ.Cell // w ∈ S} => Pcell w.1)).expect fcell := by
            calc
              _ = (FinProb.pi (fun w : {w : Γ.Cell // w ∈ S} => Pcell w.1)).expect
                    (fun a => if badCell (glue S W₀ a) then (1 : ℝ) else 0) := h.symm
              _ = (FinProb.pi (fun w : {w : Γ.Cell // w ∈ S} => Pcell w.1)).expect fcell := by
                    unfold FinProb.expect
                    apply Finset.sum_congr rfl
                    intro a ha
                    have hbad : badCell (glue S W₀ a) =
                        (¬ CrossValidRow Γ M (σ c.1)
                          (fun h => a (index h)) c.1) := by
                      dsimp [badCell]
                      rw [hproj a]
                    simp [fcell, hbad]
  have hLocalKey :
      (FinProb.pi (fun w : {w : Γ.Cell // w ∈ S} => Pcell w.1)).expect fcell =
        (FinProb.pi Pkey).expect (fun a => if badKey a then (1 : ℝ) else 0) := by
    calc
      (FinProb.pi (fun w : {w : Γ.Cell // w ∈ S} => Pcell w.1)).expect fcell =
          (FinProb.pi (fun w : {w : Γ.Cell // w ∈ S} => Pcell w.1)).expect
            (fun a => if badKey (ePi a) then (1 : ℝ) else 0) := by
              unfold FinProb.expect
              apply Finset.sum_congr rfl
              intro a ha
              have hprojKey : (fun g => a (index g)) = ePi a := by
                funext g
                simp [ePi, Equiv.piCongrLeft, eKey, index, S]
              have heq : fcell a = (if badKey (ePi a) then (1 : ℝ) else 0) := by
                dsimp [fcell, badKey]
                rw [hprojKey]
              rw [heq]
      _ = (FinProb.pi Pkey).expect (fun a => if badKey a then (1 : ℝ) else 0) := by
        simpa [ePi] using
          (pi_expect_equiv_q_s07_anchor eKey
            (fun w : {w : Γ.Cell // w ∈ S} => Pcell w.1) Pkey
            (by intro w; rfl) (fun a => if badKey a then (1 : ℝ) else 0))
  calc
    (rawAnchors Γ M σ).pr badCell =
        (rawAnchors Γ M σ).expect (fun W => if badCell W then (1 : ℝ) else 0) := by
      classical
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro W hW
      by_cases h : badCell W <;> simp [h]
    _ = (FinProb.pi (fun w : {w : Γ.Cell // w ∈ S} => Pcell w.1)).expect fcell := hRawExpect
    _ = (FinProb.pi Pkey).expect (fun a => if badKey a then (1 : ℝ) else 0) := hLocalKey
    _ = (FinProb.pi Pkey).pr badKey := by
      classical
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : badKey a <;> simp [h]
    _ = crossFailKey Γ M σ c.1 := by rfl

end HypercubeRamsey.S07
