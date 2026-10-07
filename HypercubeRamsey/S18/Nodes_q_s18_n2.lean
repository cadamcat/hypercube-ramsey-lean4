import HypercubeRamsey.S18.Transfer

namespace HypercubeRamsey.S18.Lane_q_s18_n2
open Classical
open Filter

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}

private def nearInternal (a : Fin (T.S.n k)) : Prop :=
  ∃ t ∈ PT.tiling.Icoord (D.geom.patchOf X.target),
    D.geom.ids a - D.geom.ids t ∈ D.geom.Lsub

private def sameIdCoset (D : LateData hPT) (a b : Fin (T.S.n k)) : Prop :=
  D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub

private noncomputable def idCosetClass (D : LateData hPT) (c : Fin (T.S.n k)) :
    Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun a => sameIdCoset D a c

private noncomputable def cosetParity (D : LateData hPT) (v : Pos T k)
    (c : Fin (T.S.n k)) : ZMod 2 :=
  ∑ a ∈ idCosetClass D c, if v a = true then 1 else 0

private theorem zmodTwo_double (x : ZMod 2) : x + x = 0 := by
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  calc
    x + x = (2 : ZMod 2) * x := (two_mul x).symm
    _ = 0 := by rw [htwo]; simp

private theorem syndrome_flip (v : Pos T k) (a : Fin (T.S.n k)) :
    D.geom.syndrome (flipPos v a) = D.geom.syndrome v + D.geom.ids a := by
  classical
  let f : Fin (T.S.n k) → (Fin D.geom.Hdim → ZMod 2) := fun j =>
    if v j = true then D.geom.ids j else 0
  let f' : Fin (T.S.n k) → (Fin D.geom.Hdim → ZMod 2) := fun j =>
    if flipPos v a j = true then D.geom.ids j else 0
  have ha : f' a = f a + D.geom.ids a := by
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    have hxx (x : ZMod 2) : x + x = 0 := by
      calc
        x + x = (2 : ZMod 2) * x := (two_mul x).symm
        _ = 0 := by rw [htwo]; simp
    cases hv : v a with
    | false => simp [f, f', flipPos, hv]
    | true =>
        ext j
        simp [f, f', flipPos, hv]
        exact (hxx (D.geom.ids a j)).symm
  have hother : ∀ j, j ≠ a → f' j = f j := by
    intro j hja
    simp [f, f', flipPos, hja]
  change ∑ j, f' j = (∑ j, f j) + D.geom.ids a
  calc
    ∑ j, f' j = f' a + ∑ j ∈ (Finset.univ.erase a), f' j := by
      rw [← Finset.add_sum_erase (s := Finset.univ) (f := f') (Finset.mem_univ a)]
    _ = (f a + D.geom.ids a) + ∑ j ∈ (Finset.univ.erase a), f j := by
      rw [ha]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact hother j (Finset.ne_of_mem_erase hj)
    _ = (∑ j, f j) + D.geom.ids a := by
      rw [← Finset.add_sum_erase (s := Finset.univ) (f := f) (Finset.mem_univ a)]
      abel

private theorem cosetParity_flip (D : LateData hPT) (v : Pos T k)
    (a c : Fin (T.S.n k)) :
    cosetParity D (flipPos v a) c = cosetParity D v c +
      if sameIdCoset D a c then 1 else 0 := by
  classical
  let S := idCosetClass D c
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  have hpoint (t : Fin (T.S.n k)) (ht : t ∈ S) :
      (if flipPos v a t = true then (1 : ZMod 2) else 0) =
        (if v t = true then 1 else 0) + (if t = a then 1 else 0) := by
    by_cases hta : t = a
    · subst t
      cases hv : v a
      · simp [flipPos, hv]
      · simp [flipPos, hv]
        rw [← two_mul (1 : ZMod 2), htwo]
        simp
    · cases hv : v t <;> simp [flipPos, hta, hv]
  have hsum :
      S.sum (fun t => if flipPos v a t = true then (1 : ZMod 2) else 0) =
      S.sum (fun t => if v t = true then (1 : ZMod 2) else 0) +
        S.sum (fun t => if t = a then (1 : ZMod 2) else 0) := by
    calc
      S.sum (fun t => if flipPos v a t = true then (1 : ZMod 2) else 0) =
          S.sum (fun t => (if v t = true then (1 : ZMod 2) else 0) +
            (if t = a then (1 : ZMod 2) else 0)) := by
              apply Finset.sum_congr rfl
              intro t ht
              exact hpoint t ht
      _ = S.sum (fun t => if v t = true then (1 : ZMod 2) else 0) +
            S.sum (fun t => if t = a then (1 : ZMod 2) else 0) := by rw [Finset.sum_add_distrib]
  by_cases hclass : sameIdCoset D a c
  · have hmem : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclass⟩
    have hone : (∑ t ∈ S, if t = a then (1 : ZMod 2) else 0) = 1 := by
      simp [Finset.sum_ite_eq', hmem]
    dsimp [cosetParity, S] at hsum ⊢
    rw [hsum, hone]
    simp [hclass]
  · have hnot : a ∉ S := by
      intro h
      exact hclass (Finset.mem_filter.mp h).2
    have hsum' :
        (∑ t ∈ S, if flipPos v a t = true then (1 : ZMod 2) else 0) =
          (∑ t ∈ S, if v t = true then (1 : ZMod 2) else 0) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hta : t ≠ a := by intro he; exact hnot (he ▸ ht)
      simp [flipPos, hta]
    dsimp [cosetParity, S] at hsum' ⊢
    rw [hsum']
    simp [hclass]

private theorem sameIdCoset_symm (D : LateData hPT) {a b : Fin (T.S.n k)}
    (h : sameIdCoset D a b) : sameIdCoset D b a := by
  change D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub at h
  change D.geom.ids b - D.geom.ids a ∈ D.geom.Lsub
  have heq : D.geom.ids b - D.geom.ids a = -(D.geom.ids a - D.geom.ids b) := by abel
  rw [heq]
  exact D.geom.Lsub.neg_mem h

private theorem sameIdCoset_trans (D : LateData hPT) {a b c : Fin (T.S.n k)}
    (hab : sameIdCoset D a b)
    (hbc : sameIdCoset D b c) :
    sameIdCoset D a c := by
  change D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub at hab
  change D.geom.ids b - D.geom.ids c ∈ D.geom.Lsub at hbc
  change D.geom.ids a - D.geom.ids c ∈ D.geom.Lsub
  have heq : D.geom.ids a - D.geom.ids c =
      (D.geom.ids a - D.geom.ids b) + (D.geom.ids b - D.geom.ids c) := by abel
  rw [heq]
  exact D.geom.Lsub.add_mem hab hbc

theorem patchOf_flip_bulk (a : Fin (T.S.n k))
    (ha : a ∈ PT.tiling.bulkCoords (D.geom.patchOf X.target)) :
    D.geom.patchOf (flipPos X.target a) = D.geom.patchOf X.target := by
  classical
  rcases (Finset.mem_filter.mp ha).2 with ⟨hell, _⟩
  let p := flipPos X.target a
  have hleaf : p ∈ PT.tiling.leaf (D.geom.patchOf X.target) := by
    change ∀ j : Fin (T.S.n k),
      j.val < (PT.tiling.P (D.geom.patchOf X.target)).ℓ →
        p j = (PT.tiling.w (D.geom.patchOf X.target)) j
    intro j hj
    have htarget := D.geom.patchOf_leaf X.target j hj
    have hja : j ≠ a := by
      intro h
      subst j
      omega
    simpa [p, flipPos, hja] using htarget
  obtain ⟨i₀, hi₀, huniq⟩ := hPT.tiling_valid.prefix_complete p
  have hpi : D.geom.patchOf p = i₀ := huniq (D.geom.patchOf p) (D.geom.patchOf_leaf p)
  have hii : D.geom.patchOf X.target = i₀ := huniq (D.geom.patchOf X.target) hleaf
  exact hpi.trans hii.symm

private theorem hammingDist_flip_le_one (v : Pos T k) (a : Fin (T.S.n k)) :
    hammingDist v (flipPos v a) ≤ 1 := by
  classical
  change (Finset.univ.filter (fun j : Fin (T.S.n k) => v j ≠ flipPos v a j)).card ≤ 1
  have hsub :
      (Finset.univ.filter (fun j : Fin (T.S.n k) => v j ≠ flipPos v a j)) ⊆ {a} := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_contra hja
    have hjne : j ≠ a := by simpa using hja
    apply hj
    simp [flipPos, hjne]
  calc
    _ ≤ ({a} : Finset (Fin (T.S.n k))).card := Finset.card_le_card hsub
    _ ≤ 1 := by simp

private theorem hammingDist_comm_lane (v w : Pos T k) :
    hammingDist v w = hammingDist w v := by
  classical
  change (Finset.univ.filter (fun j : Fin (T.S.n k) => v j ≠ w j)).card =
    (Finset.univ.filter (fun j : Fin (T.S.n k) => w j ≠ v j)).card
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_comm

theorem sameCell_outer_eq (v : Pos T k) (c : Fin (T.S.n k))
    (hc : c ∈ X.criticalCoords)
    (hcell : D.geom.cellOf v = D.geom.cellOf (flipPos X.target c))
    (hmargin : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (hdist : (hammingDist v (flipPos X.target c) : ℝ) ≤ (2 * D.geom.r + 4 : ℕ)) :
    ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) →
      v a = flipPos X.target c a := by
  have hcBulk : c ∈ PT.tiling.bulkCoords (D.geom.patchOf X.target) :=
    (Finset.mem_filter.mp hc).1
  have hpatchQ : D.geom.patchOf (flipPos X.target c) = D.geom.patchOf X.target :=
    patchOf_flip_bulk (D := D) (X := X) c hcBulk
  have hpatchV : D.geom.patchOf v = D.geom.patchOf X.target := by
    calc
      D.geom.patchOf v = D.geom.cellPatch (D.geom.cellOf v) :=
        (D.geom.cellOf_patch v).symm
      _ = D.geom.cellPatch (D.geom.cellOf (flipPos X.target c)) := by rw [hcell]
      _ = D.geom.patchOf (flipPos X.target c) := D.geom.cellOf_patch _
      _ = D.geom.patchOf X.target := hpatchQ
  intro a ha
  by_contra hne
  have hnot : a ∉ PT.tiling.Icoord (D.geom.patchOf v) := by
    simpa [hpatchV] using ha
  have hspacing := D.l16_valid.cell_spacing v (flipPos X.target c) hcell ⟨a, hnot, hne⟩
  have hbound : (hammingDist v (flipPos X.target c) : ℝ) ≤ (2 * D.geom.r + 4 : ℕ) := hdist
  have hmarginR : (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3 := by exact_mod_cast hmargin
  linarith

private theorem syndrome_mem_of_class (D : LateData hPT) (b : Pos T k) (j : Fin D.geom.r)
    (h : D.geom.classOf b = some j) : D.geom.syndrome b ∈ D.geom.Lsub := by
  unfold LowGeom.classOf at h
  split_ifs at h with hmem
  · exact hmem.2

private theorem sameIdCoset_of_late_two_flip (D : LateData hPT)
    (b b' : Pos T k) (j j' : Fin D.geom.r) (a a' : Fin (T.S.n k))
    (hb : D.geom.classOf b = some j) (hb' : D.geom.classOf b' = some j')
    (hflip : flipPos b a = flipPos b' a') : sameIdCoset D a a' := by
  have hsyndrome := congrArg D.geom.syndrome hflip
  rw [syndrome_flip (D := D) b a, syndrome_flip (D := D) b' a'] at hsyndrome
  have hdiff : D.geom.ids a - D.geom.ids a' =
      D.geom.syndrome b' - D.geom.syndrome b := by
    calc
      D.geom.ids a - D.geom.ids a' =
          (D.geom.syndrome b + D.geom.ids a) -
            (D.geom.syndrome b + D.geom.ids a') := by abel
      _ = (D.geom.syndrome b' + D.geom.ids a') -
            (D.geom.syndrome b + D.geom.ids a') := by rw [hsyndrome]
      _ = D.geom.syndrome b' - D.geom.syndrome b := by abel
  change D.geom.ids a - D.geom.ids a' ∈ D.geom.Lsub
  rw [hdiff]
  exact D.geom.Lsub.sub_mem (syndrome_mem_of_class D b' j' hb')
    (syndrome_mem_of_class D b j hb)

private theorem flipPos_involutive {n : ℕ} (v : CubePos n) (a : Fin n) :
    flipPos (flipPos v a) a = v := by
  funext j
  by_cases hja : j = a
  · subst j
    simp [flipPos]
  · simp [flipPos, hja]

private theorem cosetParity_flip_pair (D : LateData hPT) (v : Pos T k)
    (a a' c : Fin (T.S.n k)) (haa' : sameIdCoset D a a') :
    cosetParity D (flipPos (flipPos v a) a') c = cosetParity D v c := by
  rw [cosetParity_flip D (flipPos v a) a' c, cosetParity_flip D v a c]
  have hclass : sameIdCoset D a c ↔ sameIdCoset D a' c := by
    constructor
    · intro hac
      exact sameIdCoset_trans D (sameIdCoset_symm D haa') hac
    · intro ha'c
      exact sameIdCoset_trans D haa' ha'c
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  have hone : (1 : ZMod 2) + 1 = 0 := by
    calc
      (1 : ZMod 2) + 1 = 2 := by norm_num
      _ = 0 := htwo
  by_cases hA : sameIdCoset D a c
  · have hA' : sameIdCoset D a' c := hclass.mp hA
    simp [hA, hA', hone, add_assoc]
  · have hA' : ¬ sameIdCoset D a' c := fun h' => hA (hclass.mpr h')
    simp [hA, hA', add_assoc]

private theorem predecessors_cosetParity_eq (D : LateData hPT) (X : CriticalTransferData D) :
    ∀ n (b : Pos T k), b ∈ X.predecessors n →
      ∀ c, cosetParity D b c = cosetParity D X.failure.2.1.1 c := by
  intro n
  induction n with
  | zero =>
      intro b hb c
      simp [CriticalTransferData.predecessors] at hb
      subst b
      rfl
  | succ n ih =>
      intro b hb c
      simp only [CriticalTransferData.predecessors] at hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact ih b hb c
      · rcases Finset.mem_filter.mp hb with ⟨_, hex⟩
        rcases hex with ⟨b₀, hb₀, j, j', hj, hj', hlt, hflipExists⟩
        rcases hflipExists with ⟨a, a', hflip⟩
        have hsame := sameIdCoset_of_late_two_flip D b₀ b j j' a a' hj hj' hflip
        have hbEq : b = flipPos (flipPos b₀ a) a' := by
          have hcon := congrArg (fun w : Pos T k => flipPos w a') hflip
          rw [flipPos_involutive] at hcon
          exact hcon.symm
        rw [hbEq, cosetParity_flip_pair D b₀ a a' c hsame]
        exact ih b₀ hb₀ c

private theorem class_some_of_predecessor (D : LateData hPT) (X : CriticalTransferData D) :
    ∀ n (b : Pos T k), b ∈ X.predecessors n → ∃ j, D.geom.classOf b = some j := by
  intro n
  induction n with
  | zero =>
      intro b hb
      simp [CriticalTransferData.predecessors] at hb
      subst b
      refine ⟨X.failure.1, ?_⟩
      exact (D.encoding.base.class_of_spec X.failure.2.1.1 X.failure.1).mp X.failure.2.1.2
  | succ n ih =>
      intro b hb
      simp only [CriticalTransferData.predecessors] at hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact ih b hb
      · rcases Finset.mem_filter.mp hb with ⟨_, hex⟩
        rcases hex with ⟨_, _, _, j', _, hj', _, _⟩
        exact ⟨j', hj'⟩

private theorem notEven_of_class_some (D : LateData hPT) (b : Pos T k)
    (j : Fin D.geom.r) (h : D.geom.classOf b = some j) : ¬ IsEvenRole b := by
  unfold LowGeom.classOf at h
  split_ifs at h with hcond
  · exact hcond.1

private theorem cosetParity_mismatch_of_internal (D : LateData hPT) (X : CriticalTransferData D)
    {s t : Pos T k} (q : Fin (T.S.n k))
    (hq : q ∈ PT.tiling.Icoord (D.geom.patchOf X.target))
    (houter : ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → s a = t a) :
    cosetParity D s q + cosetParity D t q = if s q = t q then 0 else 1 := by
  classical
  let i := D.geom.patchOf X.target
  let S := idCosetClass D q
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  have hdouble (x : ZMod 2) : x + x = 0 := by
    calc
      x + x = (2 : ZMod 2) * x := (two_mul x).symm
      _ = 0 := by rw [htwo]; simp
  have hpoint (a : Fin (T.S.n k)) (ha : a ∈ S) :
      (if s a = true then (1 : ZMod 2) else 0) +
        (if t a = true then 1 else 0) =
          if a = q then (if s q = t q then 0 else 1) else 0 := by
    by_cases haq : a = q
    · subst a
      cases hs : s q <;> cases htBool : t q <;> simp [hs, htBool, hdouble]
    · have haCoset : sameIdCoset D a q := (Finset.mem_filter.mp ha).2
      have haNotI : a ∉ PT.tiling.Icoord i := by
        intro haI
        have heq : a = q :=
          D.l16_valid.internal_cosets i a q haI hq haCoset
        exact haq heq
      have hEq := houter a haNotI
      cases htBool : t a <;> simp [haq, hEq, htBool, hdouble]
  have hsum :
      S.sum (fun a => if s a = true then (1 : ZMod 2) else 0) +
        S.sum (fun a => if t a = true then (1 : ZMod 2) else 0) =
      S.sum (fun a => if a = q then (if s q = t q then 0 else 1) else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpoint
  have hmem : q ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    change D.geom.ids q - D.geom.ids q ∈ D.geom.Lsub
    simp⟩
  have hsingle :
      S.sum (fun a => if a = q then (if s q = t q then (0 : ZMod 2) else 1) else 0) =
        (if s q = t q then 0 else 1) := by
    simp [Finset.sum_ite_eq', hmem]
  simpa [cosetParity, S] using hsum.trans (by rw [hsingle])

private theorem cosetParity_eq_on_noInternalClass (D : LateData hPT) (s t : Pos T k)
    (q : Fin (T.S.n k))
    (hNo : ∀ a, a ∈ PT.tiling.Icoord (D.geom.patchOf X.target) →
      ¬ sameIdCoset D a q)
    (houter : ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → s a = t a) :
    cosetParity D s q = cosetParity D t q := by
  classical
  unfold cosetParity idCosetClass
  apply Finset.sum_congr rfl
  intro a ha
  have haClass : sameIdCoset D a q := (Finset.mem_filter.mp ha).2
  have haI : a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) := by
    intro hI
    exact hNo a hI haClass
  simpa [houter a haI]

private theorem sameIdCoset_iff_of_outer_noInternalClass (D : LateData hPT)
    (X : CriticalTransferData D) (b b0 w : Pos T k) (d a0 q : Fin (T.S.n k))
    (hb : ∀ c, cosetParity D b c = cosetParity D b0 c)
    (hw : w = flipPos b d) (htarget : X.target = flipPos b0 a0)
    (houter : ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → w a = X.target a)
    (hNo : ∀ a, a ∈ PT.tiling.Icoord (D.geom.patchOf X.target) → ¬ sameIdCoset D a q) :
    sameIdCoset D d q ↔ sameIdCoset D a0 q := by
  have houter' : ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) →
      (flipPos b d) a = (flipPos b0 a0) a := by
    intro a ha
    rw [← hw, ← htarget]
    exact houter a ha
  have hparity := cosetParity_eq_on_noInternalClass D
    (flipPos b d) (flipPos b0 a0) q hNo houter'
  have hdelta :
      (if sameIdCoset D d q then (1 : ZMod 2) else 0) =
        (if sameIdCoset D a0 q then 1 else 0) := by
    have heq : cosetParity D b q +
          (if sameIdCoset D d q then (1 : ZMod 2) else 0) =
        cosetParity D b0 q + (if sameIdCoset D a0 q then 1 else 0) := by
      calc
        _ = cosetParity D (flipPos b d) q := (cosetParity_flip D b d q).symm
        _ = cosetParity D (flipPos b0 a0) q := hparity
        _ = _ := cosetParity_flip D b0 a0 q
    rw [hb q] at heq
    exact add_left_cancel heq
  constructor
  · intro hd
    by_contra ha
    simp [hd, ha] at hdelta
  · intro ha
    by_contra hd
    simp [hd, ha] at hdelta

private theorem bool_eq_not_of_ne {x y : Bool} (h : x ≠ y) : x = !y := by
  cases x <;> cases y <;> simp_all

private theorem erased_mismatch_formula (D : LateData hPT) (X : CriticalTransferData D)
    (b b0 w : Pos T k) (d a0 : Fin (T.S.n k))
    (hPred : ∀ q, cosetParity D b q = cosetParity D b0 q)
    (hwd : w = flipPos b d) (htarget : X.target = flipPos b0 a0)
    (houter : ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → w a = X.target a)
    (q : Fin (T.S.n k)) (hq : q ∈ PT.tiling.Icoord (D.geom.patchOf X.target)) :
    (if w q = X.target q then (0 : ZMod 2) else 1) =
      (if sameIdCoset D d q then (1 : ZMod 2) else 0) +
        (if sameIdCoset D a0 q then 1 else 0) := by
  have hformula :
      cosetParity D (flipPos b d) q + cosetParity D (flipPos b0 a0) q =
        (if sameIdCoset D d q then (1 : ZMod 2) else 0) +
          (if sameIdCoset D a0 q then 1 else 0) := by
    rw [cosetParity_flip D b d q, cosetParity_flip D b0 a0 q, hPred q]
    calc
      (cosetParity D b0 q + (if sameIdCoset D d q then 1 else 0)) +
          (cosetParity D b0 q + (if sameIdCoset D a0 q then 1 else 0)) =
            (cosetParity D b0 q + cosetParity D b0 q) +
              ((if sameIdCoset D d q then 1 else 0) +
                (if sameIdCoset D a0 q then 1 else 0)) := by abel
      _ = 0 + ((if sameIdCoset D d q then 1 else 0) +
            (if sameIdCoset D a0 q then 1 else 0)) := by rw [zmodTwo_double]
      _ = (if sameIdCoset D d q then 1 else 0) +
            (if sameIdCoset D a0 q then 1 else 0) := by simp
  have hmis := cosetParity_mismatch_of_internal D X q hq houter
  calc
    (if w q = X.target q then (0 : ZMod 2) else 1) =
        cosetParity D w q + cosetParity D X.target q := hmis.symm
    _ = cosetParity D (flipPos b d) q + cosetParity D (flipPos b0 a0) q := by
      rw [hwd, htarget]
    _ = (if sameIdCoset D d q then (1 : ZMod 2) else 0) +
          (if sameIdCoset D a0 q then 1 else 0) := hformula

theorem erased_internal_field (D : LateData hPT) (X : CriticalTransferData D) :
    X.erased ⊆ {X.target} ∨
      ∃ a ∈ PT.tiling.Icoord (D.geom.patchOf X.target),
        X.erased ⊆ (PT.tiling.Icoord (D.geom.patchOf X.target)).image
          (flipPos (flipPos X.target a)) := by
  classical
  let b0 : Pos T k := X.failure.2.1.1
  let a0 : Fin (T.S.n k) := X.failure.2.2.2.2
  let i := D.geom.patchOf X.target
  have htarget : X.target = flipPos b0 a0 := rfl
  have hpred (b : Pos T k) (hb : b ∈ X.predecessors D.geom.r) :
      ∀ q, cosetParity D b q = cosetParity D b0 q := by
    intro q
    exact predecessors_cosetParity_eq D X D.geom.r b hb q
  by_cases hrep : nearInternal (D := D) (X := X) a0
  · rcases hrep with ⟨q0, hq0, hA0q0⟩
    have hq0A0 : sameIdCoset D q0 a0 := sameIdCoset_symm D hA0q0
    have hA0Iff (q : Fin (T.S.n k)) (hq : q ∈ PT.tiling.Icoord i) :
        sameIdCoset D a0 q ↔ q = q0 := by
      constructor
      · intro hA0q
        have hq0q := sameIdCoset_trans D hq0A0 hA0q
        exact (D.l16_valid.internal_cosets i q0 q hq0 hq hq0q).symm
      · intro hq
        subst q
        exact hA0q0
    right
    refine ⟨q0, hq0, ?_⟩
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwDirect, houter⟩
    rcases Finset.mem_biUnion.mp hwDirect with ⟨b, hb, hflipSet⟩
    rcases Finset.mem_image.mp hflipSet with ⟨d, _, hwd⟩
    have houterBD : ∀ q, q ∉ PT.tiling.Icoord i → flipPos b d q = X.target q := by
      intro q hq
      calc
        flipPos b d q = w q := congrFun hwd q
        _ = X.target q := houter q hq
    have hMismatch (q : Fin (T.S.n k)) (hq : q ∈ PT.tiling.Icoord i) :
        (if flipPos b d q = X.target q then (0 : ZMod 2) else 1) =
          (if sameIdCoset D d q then (1 : ZMod 2) else 0) +
            (if sameIdCoset D a0 q then 1 else 0) := by
      exact erased_mismatch_formula D X b b0 (flipPos b d) d a0 (hpred b hb)
        rfl htarget houterBD q hq
    by_cases hdq0 : sameIdCoset D d q0
    · have hDqIff (q : Fin (T.S.n k)) (hq : q ∈ PT.tiling.Icoord i) :
          sameIdCoset D d q ↔ q = q0 := by
        constructor
        · intro hdq
          have hq0q := sameIdCoset_trans D (sameIdCoset_symm D hdq0) hdq
          exact (D.l16_valid.internal_cosets i q0 q hq0 hq hq0q).symm
        · intro hq
          subst q
          exact hdq0
      have hword : w = X.target := by
        funext q
        by_cases hqI : q ∈ PT.tiling.Icoord i
        · have hZero : (if sameIdCoset D d q then (1 : ZMod 2) else 0) +
              (if sameIdCoset D a0 q then 1 else 0) = 0 := by
            by_cases hq0' : q = q0
            · have hd : sameIdCoset D d q := (hDqIff q hqI).mpr hq0'
              have ha : sameIdCoset D a0 q := (hA0Iff q hqI).mpr hq0'
              simp [hd, ha, zmodTwo_double]
            · have hd : ¬ sameIdCoset D d q := by
                intro h
                exact hq0' ((hDqIff q hqI).mp h)
              have ha : ¬ sameIdCoset D a0 q := by
                intro h
                exact hq0' ((hA0Iff q hqI).mp h)
              simp [hd, ha]
          have hEqFlip : flipPos b d q = X.target q := by
            by_contra hne
            have hm := hMismatch q hqI
            simp [hne, hZero] at hm
          exact (congrFun hwd q).symm.trans hEqFlip
        · exact houter q hqI
      have hwt : w = X.target := hword
      apply Finset.mem_image.mpr
      refine ⟨q0, hq0, ?_⟩
      rw [hwt]
      exact flipPos_involutive X.target q0
    · have hnearD : nearInternal (D := D) (X := X) d := by
        by_contra hNoNear
        have hNo : ∀ q, q ∈ PT.tiling.Icoord i → ¬ sameIdCoset D q d := by
          intro q hq hqd
          exact hNoNear ⟨q, hq, sameIdCoset_symm D hqd⟩
        have hiff := sameIdCoset_iff_of_outer_noInternalClass D X b b0 w d a0 d
          (hpred b hb) hwd.symm htarget houter hNo
        have hdd : sameIdCoset D d d := by
          change D.geom.ids d - D.geom.ids d ∈ D.geom.Lsub
          simp
        have hA0d := hiff.mp hdd
        have hq0d := sameIdCoset_trans D hq0A0 hA0d
        exact hdq0 (sameIdCoset_symm D hq0d)
      rcases hnearD with ⟨q1, hq1, hdq1⟩
      have hqneq : q1 ≠ q0 := by
        intro h
        subst q1
        exact hdq0 hdq1
      have hDqIff (q : Fin (T.S.n k)) (hq : q ∈ PT.tiling.Icoord i) :
          sameIdCoset D d q ↔ q = q1 := by
        constructor
        · intro hdq
          have hq1q := sameIdCoset_trans D (sameIdCoset_symm D hdq1) hdq
          exact (D.l16_valid.internal_cosets i q1 q hq1 hq hq1q).symm
        · intro hq
          subst q
          exact hdq1
      have hDiff (q : Fin (T.S.n k)) (hq : q ∈ PT.tiling.Icoord i) :
          (flipPos b d q ≠ X.target q) ↔ q = q0 ∨ q = q1 := by
        have hbits := hMismatch q hq
        rw [hDqIff q hq, hA0Iff q hq] at hbits
        constructor
        · intro hne
          by_cases hq0' : q = q0
          · exact Or.inl hq0'
          · by_cases hq1' : q = q1
            · exact Or.inr hq1'
            · simp [hne, hq0', hq1'] at hbits
        · intro hcase
          rcases hcase with hq0' | hq1'
          · subst q
            have hneq' : q0 ≠ q1 := hqneq.symm
            intro heq
            simp [heq, hneq'] at hbits
          · subst q
            intro heq
            simp [heq, hqneq] at hbits
      have hword : w = flipPos (flipPos X.target q0) q1 := by
        funext q
        by_cases hqI : q ∈ PT.tiling.Icoord i
        · by_cases hq0' : q = q0
          · subst q
            have hneq := (hDiff q0 hq0).2 (Or.inl rfl)
            have hneqW : w q0 ≠ X.target q0 := by
              intro heq
              exact hneq ((congrFun hwd q0).trans heq)
            rw [bool_eq_not_of_ne hneqW]
            have hq0q1 : q0 ≠ q1 := hqneq.symm
            simp [flipPos, hq0q1]
          · by_cases hq1' : q = q1
            · subst q
              have hneq := (hDiff q1 hq1).2 (Or.inr rfl)
              have hneqW : w q1 ≠ X.target q1 := by
                intro heq
                exact hneq ((congrFun hwd q1).trans heq)
              rw [bool_eq_not_of_ne hneqW]
              simp [flipPos, hqneq]
            · have hEq : flipPos b d q = X.target q := by
                by_contra hne
                rcases (hDiff q hqI).1 hne with hh | hh
                · exact hq0' hh
                · exact hq1' hh
              have hW : w q = X.target q := (congrFun hwd q).symm.trans hEq
              rw [hW]
              simp [flipPos, hq0', hq1']
        · rw [houter q hqI]
          have hq0' : q ≠ q0 := by intro h; exact hqI (h ▸ hq0)
          have hq1' : q ≠ q1 := by intro h; exact hqI (h ▸ hq1)
          simp [flipPos, hq0', hq1']
      have hwt : w = flipPos (flipPos X.target q0) q1 := hword
      apply Finset.mem_image.mpr
      refine ⟨q1, hq1, ?_⟩
      exact hwt.symm
  · have hNoA0 : ∀ q, q ∈ PT.tiling.Icoord i → ¬ sameIdCoset D q a0 := by
      intro q hq hqa0
      exact hrep ⟨q, hq, sameIdCoset_symm D hqa0⟩
    left
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwDirect, houter⟩
    rcases Finset.mem_biUnion.mp hwDirect with ⟨b, hb, hflipSet⟩
    rcases Finset.mem_image.mp hflipSet with ⟨d, _, hwd⟩
    have houterBD : ∀ q, q ∉ PT.tiling.Icoord i → flipPos b d q = X.target q := by
      intro q hq
      calc
        flipPos b d q = w q := congrFun hwd q
        _ = X.target q := houter q hq
    have hPred := hpred b hb
    have hMismatch (q : Fin (T.S.n k)) (hq : q ∈ PT.tiling.Icoord i) :
        (if flipPos b d q = X.target q then (0 : ZMod 2) else 1) =
          (if sameIdCoset D d q then (1 : ZMod 2) else 0) +
            (if sameIdCoset D a0 q then 1 else 0) := by
      exact erased_mismatch_formula D X b b0 (flipPos b d) d a0 hPred rfl htarget houterBD q hq
    have hNo : ∀ q, q ∈ PT.tiling.Icoord i → ¬ sameIdCoset D q a0 := hNoA0
    have hiff := sameIdCoset_iff_of_outer_noInternalClass D X b b0 w d a0 a0
      hPred hwd.symm htarget houter hNo
    have hSelf : sameIdCoset D a0 a0 := by
      change D.geom.ids a0 - D.geom.ids a0 ∈ D.geom.Lsub
      simp
    have hD0 : sameIdCoset D d a0 := hiff.mpr hSelf
    have hword : w = X.target := by
      funext q
      by_cases hq : q ∈ PT.tiling.Icoord i
      · have hA0q : ¬ sameIdCoset D a0 q := by
          intro hA0q
          exact hNoA0 q hq (sameIdCoset_symm D hA0q)
        have hDq : ¬ sameIdCoset D d q := by
          intro hdq
          exact hA0q (sameIdCoset_trans D (sameIdCoset_symm D hD0) hdq)
        have hm := hMismatch q hq
        have hEq : flipPos b d q = X.target q := by
          by_contra hne
          simp [hne, hDq, hA0q] at hm
        exact (congrFun hwd q).symm.trans hEq
      · exact houter q hq
    exact Finset.mem_singleton.mpr hword

private theorem nearInternal_transport {a b : Fin (T.S.n k)}
    (hab : D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub)
    (ha : nearInternal (D := D) (X := X) a) : nearInternal (D := D) (X := X) b := by
  rcases ha with ⟨t, ht, hat⟩
  refine ⟨t, ht, ?_⟩
  have hba : D.geom.ids b - D.geom.ids a ∈ D.geom.Lsub := by
    have heq' : D.geom.ids b - D.geom.ids a = -(D.geom.ids a - D.geom.ids b) := by abel
    rw [heq']
    exact D.geom.Lsub.neg_mem hab
  have heq : D.geom.ids b - D.geom.ids t =
      (D.geom.ids b - D.geom.ids a) + (D.geom.ids a - D.geom.ids t) := by abel
  rw [heq]
  exact D.geom.Lsub.add_mem hba hat

theorem sameBlock_symm {a b : Fin (T.S.n k)} (h : X.sameBlock a b) : X.sameBlock b a := by
  change (D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub ∨
    (nearInternal (D := D) (X := X) a ∧ nearInternal (D := D) (X := X) b)) at h
  change (D.geom.ids b - D.geom.ids a ∈ D.geom.Lsub ∨
    (nearInternal (D := D) (X := X) b ∧ nearInternal (D := D) (X := X) a))
  rcases h with hab | ⟨ha, hb⟩
  · left
    have heq : D.geom.ids b - D.geom.ids a = -(D.geom.ids a - D.geom.ids b) := by abel
    rw [heq]
    exact D.geom.Lsub.neg_mem hab
  · exact Or.inr ⟨hb, ha⟩

theorem sameBlock_trans {a b c : Fin (T.S.n k)}
    (hab : X.sameBlock a b) (hbc : X.sameBlock b c) : X.sameBlock a c := by
  change (D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub ∨
    (nearInternal (D := D) (X := X) a ∧ nearInternal (D := D) (X := X) b)) at hab
  change (D.geom.ids b - D.geom.ids c ∈ D.geom.Lsub ∨
    (nearInternal (D := D) (X := X) b ∧ nearInternal (D := D) (X := X) c)) at hbc
  change (D.geom.ids a - D.geom.ids c ∈ D.geom.Lsub ∨
    (nearInternal (D := D) (X := X) a ∧ nearInternal (D := D) (X := X) c))
  rcases hab with hab | ⟨ha, hb⟩
  · rcases hbc with hbc | ⟨hb, hc⟩
    · left
      have heq : D.geom.ids a - D.geom.ids c =
          (D.geom.ids a - D.geom.ids b) + (D.geom.ids b - D.geom.ids c) := by abel
      rw [heq]
      exact D.geom.Lsub.add_mem hab hbc
    · right
      exact ⟨nearInternal_transport (D := D) (X := X) (a := b) (b := a)
        (by
          have heq : D.geom.ids b - D.geom.ids a =
              -(D.geom.ids a - D.geom.ids b) := by abel
          rw [heq]
          exact D.geom.Lsub.neg_mem hab) hb, hc⟩
  · rcases hbc with hbc | ⟨hb', hc⟩
    · right
      exact ⟨ha, nearInternal_transport (D := D) (X := X) (a := b) (b := c) hbc hb⟩
    · right
      exact ⟨ha, hc⟩

private theorem cosetParity_eq_of_outer_no_internal (D : LateData hPT)
    (X : CriticalTransferData D) (s t : Pos T k) (q : Fin (T.S.n k))
    (houter : ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → s a = t a)
    (hnotNear : ¬ nearInternal (D := D) (X := X) q) :
    cosetParity D s q = cosetParity D t q := by
  classical
  unfold cosetParity
  apply Finset.sum_congr rfl
  intro a ha
  have hnotI : a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) := by
    intro haI
    have haq : sameIdCoset D q a := sameIdCoset_symm D (Finset.mem_filter.mp ha).2
    exact hnotNear ⟨a, haI, haq⟩
  rw [houter a hnotI]

private theorem cosetParity_doubleFlip (D : LateData hPT) (v : Pos T k)
    (a b q : Fin (T.S.n k)) :
    cosetParity D (flipPos (flipPos v a) b) q =
      cosetParity D v q + (if sameIdCoset D a q then (1 : ZMod 2) else 0) +
        (if sameIdCoset D b q then 1 else 0) := by
  rw [cosetParity_flip D (flipPos v a) b q, cosetParity_flip D v a q]

private theorem externalEarly_not_sameIdCoset (D : LateData hPT)
    (b : Pos T k) (d j : Fin (T.S.n k))
    (hb : ∃ i, D.geom.classOf b = some i)
    (hj : j ∈ D.externalEarly (flipPos b d)) :
    ¬ sameIdCoset D d j := by
  classical
  rcases hb with ⟨i, hclass⟩
  have hbOdd := notEven_of_class_some D b i hclass
  have hwEven : IsEvenRole (flipPos b d) := by
    exact (HypercubeRamsey.S15.evenRole_flipPos b d).mpr hbOdd
  have hvOdd : ¬ IsEvenRole (flipPos (flipPos b d) j) := by
    intro hvEven
    exact ((HypercubeRamsey.S15.evenRole_flipPos (flipPos b d) j).mp hvEven) hwEven
  have hnone : D.geom.classOf (flipPos (flipPos b d) j) = none :=
    (Finset.mem_filter.mp hj).2.2
  have hnotSyndrome : D.geom.syndrome (flipPos (flipPos b d) j) ∉ D.geom.Lsub := by
    by_contra hs
    unfold LowGeom.classOf at hnone
    have hcond : ¬ IsEvenRole (flipPos (flipPos b d) j) ∧
        D.geom.syndrome (flipPos (flipPos b d) j) ∈ D.geom.Lsub := ⟨hvOdd, hs⟩
    simp [hcond] at hnone
  have hbSyndrome : D.geom.syndrome b ∈ D.geom.Lsub := syndrome_mem_of_class D b i hclass
  intro hdj
  have hneg (x : ZMod 2) : -x = x := by
    calc
      -x = -x + (x + x) := by rw [zmodTwo_double]; simp
      _ = x := by abel
  have hid : D.geom.ids d + D.geom.ids j ∈ D.geom.Lsub := by
    have heq : D.geom.ids d + D.geom.ids j = D.geom.ids d - D.geom.ids j := by
      ext q
      simp only [Pi.add_apply, Pi.sub_apply]
      rw [sub_eq_add_neg, hneg]
    rw [heq]
    exact hdj
  have hsum : D.geom.syndrome b + D.geom.ids d + D.geom.ids j ∈ D.geom.Lsub := by
    have htemp : D.geom.syndrome b + (D.geom.ids d + D.geom.ids j) ∈ D.geom.Lsub :=
      D.geom.Lsub.add_mem hbSyndrome hid
    simpa only [add_assoc] using htemp
  have hformula : D.geom.syndrome (flipPos (flipPos b d) j) =
      D.geom.syndrome b + D.geom.ids d + D.geom.ids j := by
    rw [syndrome_flip, syndrome_flip]
  exact hnotSyndrome (hformula ▸ hsum)

private theorem critical_not_sameIdCoset (D : LateData hPT) (X : CriticalTransferData D)
    (a : Fin (T.S.n k)) (ha : a ∈ X.criticalCoords)
    (b₀ : Pos T k) (a₀ : Fin (T.S.n k))
    (htarget : X.target = flipPos b₀ a₀)
    (hb₀ : ∃ i, D.geom.classOf b₀ = some i) :
    ¬ sameIdCoset D a a₀ := by
  rcases hb₀ with ⟨i, hclass⟩
  have hbSyndrome := syndrome_mem_of_class D b₀ i hclass
  have hcritical := (Finset.mem_filter.mp ha).2.1
  intro haa₀
  have heq : D.geom.ids a - D.geom.syndrome X.target =
      (D.geom.ids a - D.geom.ids a₀) - D.geom.syndrome b₀ := by
    rw [htarget, syndrome_flip]
    abel
  apply hcritical
  rw [heq]
  exact D.geom.Lsub.sub_mem haa₀ hbSyndrome

private theorem cosetParity_doubleFlip_sum (D : LateData hPT)
    (b b₀ : Pos T k) (d j a₀ c q : Fin (T.S.n k))
    (hparity : cosetParity D b q = cosetParity D b₀ q) :
    cosetParity D (flipPos (flipPos b d) j) q +
        cosetParity D (flipPos (flipPos b₀ a₀) c) q =
      (if sameIdCoset D d q then (1 : ZMod 2) else 0) +
        (if sameIdCoset D j q then 1 else 0) +
        (if sameIdCoset D a₀ q then 1 else 0) +
        (if sameIdCoset D c q then 1 else 0) := by
  rw [cosetParity_doubleFlip D b d j q, cosetParity_doubleFlip D b₀ a₀ c q,
    hparity]
  calc
    _ = (cosetParity D b₀ q + cosetParity D b₀ q) +
        ((if sameIdCoset D d q then (1 : ZMod 2) else 0) +
          (if sameIdCoset D j q then 1 else 0) +
          (if sameIdCoset D a₀ q then 1 else 0) +
          (if sameIdCoset D c q then 1 else 0)) := by abel
    _ = _ := by rw [zmodTwo_double]; simp

private theorem outer_cancel_same_flip (w t : Pos T k) (j : Fin (T.S.n k))
    (hj : j ∉ PT.tiling.Icoord (D.geom.patchOf X.target))
    (houter : ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) →
      flipPos w j a = flipPos t j a) :
    ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → w a = t a := by
  intro a ha
  by_cases hja : a = j
  · subst a
    have heq := houter j hj
    simp [flipPos] at heq
    cases hw : w j <;> cases ht : t j <;> simp [hw, ht] at heq ⊢
  · have heq := houter a ha
    simpa [flipPos, hja] using heq

private theorem notErased_outer_mismatch (D : LateData hPT) (X : CriticalTransferData D)
    (w : Pos T k) (hw : w ∈ X.directEven \ X.erased) :
    ¬ ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) → w a = X.target a := by
  intro houter
  apply (Finset.mem_sdiff.mp hw).2
  exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hw).1, houter⟩

theorem bulkCoord_eq_of_cellEq {a b : Fin (T.S.n k)}
    (hlog : (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3)
    (ha : a ∈ PT.tiling.bulkCoords (D.geom.patchOf X.target))
    (hb : b ∈ PT.tiling.bulkCoords (D.geom.patchOf X.target))
    (hcell : D.geom.cellOf (flipPos X.target a) = D.geom.cellOf (flipPos X.target b)) :
    a = b := by
  classical
  let i := D.geom.patchOf X.target
  change a ∈ PT.tiling.bulkCoords i at ha
  change b ∈ PT.tiling.bulkCoords i at hb
  rcases (Finset.mem_filter.mp ha).2 with ⟨hell_a, hnotI_a⟩
  rcases (Finset.mem_filter.mp hb).2 with ⟨hell_b, hnotI_b⟩
  let pa := flipPos X.target a
  let pb := flipPos X.target b
  have hleaf_a : pa ∈ PT.tiling.leaf i := by
    change ∀ j : Fin (T.S.n k), j.val < (PT.tiling.P i).ℓ → pa j = (PT.tiling.w i) j
    intro j hj
    have htarget := D.geom.patchOf_leaf X.target j hj
    have hja : j ≠ a := by
      intro h
      subst j
      omega
    simpa [pa, flipPos, hja] using htarget
  have hleaf_b : pb ∈ PT.tiling.leaf i := by
    change ∀ j : Fin (T.S.n k), j.val < (PT.tiling.P i).ℓ → pb j = (PT.tiling.w i) j
    intro j hj
    have htarget := D.geom.patchOf_leaf X.target j hj
    have hjb : j ≠ b := by
      intro h
      subst j
      omega
    simpa [pb, flipPos, hjb] using htarget
  have hpatch_a : D.geom.patchOf pa = i := by
    obtain ⟨i₀, hi₀, huniq⟩ := hPT.tiling_valid.prefix_complete pa
    exact (huniq (D.geom.patchOf pa) (D.geom.patchOf_leaf pa)).trans
      (huniq i hleaf_a).symm
  have hpatch_b : D.geom.patchOf pb = i := by
    obtain ⟨i₀, hi₀, huniq⟩ := hPT.tiling_valid.prefix_complete pb
    exact (huniq (D.geom.patchOf pb) (D.geom.patchOf_leaf pb)).trans
      (huniq i hleaf_b).symm
  by_contra hab
  have hposne : pa a ≠ pb a := by
    dsimp [pa, pb]
    simp [flipPos, hab]
  have hspacing := D.l16_valid.cell_spacing pa pb hcell ⟨a, by simpa [hpatch_a] using hnotI_a, hposne⟩
  have hdist : hammingDist pa pb ≤ 2 := by
    change (Finset.univ.filter (fun j : Fin (T.S.n k) => pa j ≠ pb j)).card ≤ 2
    have hsub : (Finset.univ.filter (fun j : Fin (T.S.n k) => pa j ≠ pb j)) ⊆ {a, b} := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_cases hja : j = a
      · simp [hja]
      · by_cases hjb : j = b
        · simp [hjb]
        · have hpa : pa j = X.target j := by simpa [pa, flipPos, hja]
          have hpb : pb j = X.target j := by simpa [pb, flipPos, hjb]
          exact (hj (hpa.trans hpb.symm)).elim
    calc
      _ ≤ ({a, b} : Finset (Fin (T.S.n k))).card := Finset.card_le_card hsub
      _ ≤ 2 := by by_cases hab' : a = b <;> simp [hab']
  have hdistR : (hammingDist pa pb : ℝ) ≤ 2 := by exact_mod_cast hdist
  linarith

theorem criticalCoord_eq_of_cellEq {a b : Fin (T.S.n k)}
    (hlog : (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3)
    (ha : a ∈ X.criticalCoords) (hb : b ∈ X.criticalCoords)
    (hcell : D.geom.cellOf (flipPos X.target a) = D.geom.cellOf (flipPos X.target b)) :
    a = b := by
  exact bulkCoord_eq_of_cellEq (D := D) (X := X) hlog
    (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hcell

theorem blockCells_disjoint_of_not_sameBlock {a b : Fin (T.S.n k)}
    (hlog : (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3)
    (hab : ¬ X.sameBlock a b) : Disjoint (X.blockCells a) (X.blockCells b) := by
  apply Finset.disjoint_left.mpr
  intro C hCa hCb
  rcases Finset.mem_image.mp hCa with ⟨u, hu, rfl⟩
  rcases Finset.mem_image.mp hCb with ⟨v, hv, hcv⟩
  have huv := criticalCoord_eq_of_cellEq (D := D) (X := X) hlog
    (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hv).1 hcv.symm
  have hAu : X.sameBlock a u := (Finset.mem_filter.mp hu).2
  have hBv : X.sameBlock b v := (Finset.mem_filter.mp hv).2
  have hBu : X.sameBlock b u := by simpa [huv] using hBv
  exact hab (sameBlock_trans hAu (sameBlock_symm hBu))

private noncomputable def activeTrace (P : TransferProtocol X) (seed : P.Seed)
    (a : Fin (T.S.n k)) (s : X.Raw) : List (Fin P.steps × P.Reply) :=
  ((Finset.univ : Finset (Fin P.steps)).filter fun t =>
    X.sameBlock a (P.request seed (P.replies seed s t.val))).toList.map fun t =>
      (t, P.answer seed (P.replies seed s t.val) s)

private theorem activeTrace_mem (P : TransferProtocol X) (seed : P.Seed)
    (a : Fin (T.S.n k)) (s : X.Raw) (t : Fin P.steps)
    (ha : X.sameBlock a (P.request seed (P.replies seed s t.val))) :
    (t, P.answer seed (P.replies seed s t.val) s) ∈ activeTrace P seed a s := by
  unfold activeTrace
  apply List.mem_map.mpr
  refine ⟨t, ?_, rfl⟩
  exact Finset.mem_toList.mpr <| Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩

private theorem activeTrace_length_le (P : TransferProtocol X) (seed : P.Seed)
    (a : Fin (T.S.n k)) (s : X.Raw) :
    (activeTrace P seed a s).length ≤ ⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ := by
  have hcard :
      ((Finset.univ : Finset (Fin P.steps)).filter fun t =>
        X.sameBlock a (P.request seed (P.replies seed s t.val))).card =
      ((Finset.range P.steps).filter fun t =>
        X.sameBlock a (P.request seed (P.replies seed s t))).card := by
    apply Finset.card_bij (fun t _ => t.val)
    · intro t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr t.isLt, (Finset.mem_filter.mp ht).2⟩
    · intro t₁ ht₁ t₂ ht₂ heq
      exact Fin.ext heq
    · intro t ht
      rcases Finset.mem_filter.mp ht with ⟨htRange, hactive⟩
      refine ⟨⟨t, Finset.mem_range.mp htRange⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hactive⟩
  calc
    (activeTrace P seed a s).length =
        ((Finset.univ : Finset (Fin P.steps)).filter fun t =>
          X.sameBlock a (P.request seed (P.replies seed s t.val))).card := by
            simp [activeTrace]
    _ = ((Finset.range P.steps).filter fun t =>
          X.sameBlock a (P.request seed (P.replies seed s t))).card := hcard
    _ ≤ ⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ := P.calls_bound seed s a

private abbrev BoundedLists (α : Type*) (M : ℕ) := {l : List α // l.length ≤ M}

private def boundedListCode {α : Type*} [Fintype α] (M : ℕ) :
    BoundedLists α M → Fin (M + 1) × (Fin M → Option α) := fun l =>
  (⟨l.1.length, by omega⟩, fun i => l.1[i.val]?)

private theorem boundedListCode_injective {α : Type*} [Fintype α] (M : ℕ) :
    Function.Injective (boundedListCode (α := α) M) := by
  intro l₁ l₂ h
  apply Subtype.ext
  have hlen : l₁.1.length = l₂.1.length := congrArg (fun p => p.1.val) h
  have hfun : (fun i : Fin M => l₁.1[i.val]?) = (fun i : Fin M => l₂.1[i.val]?) :=
    congrArg Prod.snd h
  apply List.ext_getElem?'
  intro n hn
  have hnM : n < M := by
    have hn' : n < max l₁.1.length l₂.1.length := hn
    rw [hlen] at hn'
    omega
  simpa [boundedListCode] using congrFun hfun ⟨n, hnM⟩

noncomputable instance boundedListsFintype {α : Type*} [Fintype α] (M : ℕ) :
    Fintype (BoundedLists α M) :=
  Fintype.ofInjective (boundedListCode (α := α) M) (boundedListCode_injective (α := α) M)

private theorem boundedLists_card_le {α : Type*} [Fintype α] (M : ℕ) :
    Fintype.card (BoundedLists α M) ≤ (M + 1) * (Fintype.card α + 1) ^ M := by
  calc
    Fintype.card (BoundedLists α M) ≤
        Fintype.card (Fin (M + 1) × (Fin M → Option α)) :=
      Fintype.card_le_of_injective (boundedListCode (α := α) M)
        (boundedListCode_injective (α := α) M)
    _ = (M + 1) * (Fintype.card α + 1) ^ M := by simp

private theorem card_image_le_card_of_factor {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (S : Finset α)
    (f : α → β) (g : α → γ)
    (hfactor : ∀ a, a ∈ S → ∀ b, b ∈ S → g a = g b → f a = f b) :
    (S.image f).card ≤ (S.image g).card := by
  classical
  let pre : {y : β // y ∈ S.image f} → α := fun y => Classical.choose (Finset.mem_image.mp y.2)
  have hpre (y : {y : β // y ∈ S.image f}) : pre y ∈ S ∧ f (pre y) = y.1 :=
    Classical.choose_spec (Finset.mem_image.mp y.2)
  let mapImage : {y : β // y ∈ S.image f} → {z : γ // z ∈ S.image g} := fun y =>
    ⟨g (pre y), Finset.mem_image.mpr ⟨pre y, (hpre y).1, rfl⟩⟩
  have hmap : Function.Injective mapImage := by
    intro y z hyz
    apply Subtype.ext
    have hgz : g (pre y) = g (pre z) := congrArg Subtype.val hyz
    have hfz := hfactor (pre y) (hpre y).1 (pre z) (hpre z).1 hgz
    calc
      y.1 = f (pre y) := (hpre y).2.symm
      _ = f (pre z) := hfz
      _ = z.1 := (hpre z).2
  have hcard := Fintype.card_le_of_injective mapImage hmap
  simpa using hcard

private noncomputable def activeTraceCode (P : TransferProtocol X) (seed : P.Seed)
    (a : Fin (T.S.n k)) (s : X.Raw) :=
  let M := ⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊
  boundedListCode (M := M)
    (⟨activeTrace P seed a s, activeTrace_length_le P seed a s⟩ :
      BoundedLists (Fin P.steps × P.Reply) M)

private theorem activeTrace_eq_of_code_eq (P : TransferProtocol X) (seed : P.Seed)
    (a : Fin (T.S.n k)) (s s' : X.Raw)
    (hcode : activeTraceCode P seed a s = activeTraceCode P seed a s') :
    activeTrace P seed a s = activeTrace P seed a s' := by
  let M := ⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊
  have hsub :
      (⟨activeTrace P seed a s, activeTrace_length_le P seed a s⟩ :
        BoundedLists (Fin P.steps × P.Reply) M) =
      ⟨activeTrace P seed a s', activeTrace_length_le P seed a s'⟩ :=
    boundedListCode_injective (α := Fin P.steps × P.Reply) M hcode
  exact congrArg Subtype.val hsub

theorem replies_eq_of_activeTrace_eq (P : TransferProtocol X) (seed : P.Seed)
    (a : Fin (T.S.n k)) (hlog : (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3)
    {s s' : X.Raw} (hout : ∀ C, C ∉ X.blockCells a → s C = s' C)
    (htrace : activeTrace P seed a s = activeTrace P seed a s') :
    P.replies seed s P.steps = P.replies seed s' P.steps := by
  have hprefix : ∀ t, t ≤ P.steps → P.replies seed s t = P.replies seed s' t := by
    intro t
    induction t with
    | zero =>
        intro _
        simp [P.replies_zero]
    | succ t ih =>
        intro ht
        have hlt : t < P.steps := by omega
        have hp := ih (by omega)
        let q : Fin P.steps := ⟨t, hlt⟩
        by_cases hactive : X.sameBlock a (P.request seed (P.replies seed s t))
        · have hmem := activeTrace_mem P seed a s q (by simpa [q] using hactive)
          have hmem' : (q, P.answer seed (P.replies seed s q.val) s) ∈ activeTrace P seed a s' := by
            rw [← htrace]
            exact hmem
          unfold activeTrace at hmem'
          rcases List.mem_map.mp hmem' with ⟨t', ht', heq⟩
          have htEq : t' = q := congrArg Prod.fst heq
          subst t'
          have hanswer : P.answer seed (P.replies seed s q.val) s =
              P.answer seed (P.replies seed s' q.val) s' := (congrArg Prod.snd heq).symm
          have hanswer' : P.answer seed (P.replies seed s' t) s =
              P.answer seed (P.replies seed s' t) s' := by simpa [q, hp] using hanswer
          calc
            P.replies seed s (t + 1) =
                P.replies seed s t ++ [P.answer seed (P.replies seed s t) s] := P.replies_step seed s t
            _ = P.replies seed s' t ++ [P.answer seed (P.replies seed s' t) s'] := by rw [hp, hanswer']
            _ = P.replies seed s' (t + 1) := (P.replies_step seed s' t).symm
        · have hdisj := blockCells_disjoint_of_not_sameBlock (D := D) (X := X) hlog hactive
          have hlocal : P.answer seed (P.replies seed s t) s =
              P.answer seed (P.replies seed s t) s' :=
            P.answer_local seed (P.replies seed s t) s s' (by
            intro C hC
            have hnot : C ∉ X.blockCells a := by
              intro hCa
              exact (Finset.disjoint_left.mp hdisj) hCa hC
            exact hout C hnot)
          have hanswer : P.answer seed (P.replies seed s' t) s =
              P.answer seed (P.replies seed s' t) s' := by simpa [hp] using hlocal
          calc
            P.replies seed s (t + 1) =
                P.replies seed s t ++ [P.answer seed (P.replies seed s t) s] := P.replies_step seed s t
            _ = P.replies seed s' t ++ [P.answer seed (P.replies seed s' t) s'] := by rw [hp, hanswer]
            _ = P.replies seed s' (t + 1) := (P.replies_step seed s' t).symm
  exact hprefix P.steps le_rfl

private theorem hammingDist_le_two_of_flipEq {v w : Pos T k}
    (a a' : Fin (T.S.n k)) (hflip : flipPos v a = flipPos w a') :
    hammingDist v w ≤ 2 := by
  classical
  change (Finset.univ.filter (fun j : Fin (T.S.n k) => v j ≠ w j)).card ≤ 2
  have hsub :
      (Finset.univ.filter (fun j : Fin (T.S.n k) => v j ≠ w j)) ⊆ {a, a'} := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_cases hja : j = a
    · simp [hja]
    · by_cases hja' : j = a'
      · simp [hja']
      · exfalso
        apply hj
        have hvj : flipPos v a j = v j := by simp [flipPos, hja]
        have hwj : flipPos w a' j = w j := by simp [flipPos, hja']
        calc
          v j = flipPos v a j := hvj.symm
          _ = flipPos w a' j := congrFun hflip j
          _ = w j := hwj
  calc
    _ ≤ ({a, a'} : Finset (Fin (T.S.n k))).card := Finset.card_le_card hsub
    _ ≤ 2 := by by_cases haa : a = a' <;> simp [haa]

theorem predecessor_radius (b : Pos T k) (hb :
    b ∈ X.predecessors D.geom.r) :
    b ∈ cubeBall X.failure.2.1.1 (2 * D.geom.r) := by
  have hdist : ∀ n (b : Pos T k), b ∈ X.predecessors n →
      hammingDist X.failure.2.1.1 b ≤ 2 * n := by
    intro n
    induction n with
    | zero =>
        intro b hb
        simp [CriticalTransferData.predecessors] at hb
        subst b
        simp [hammingDist]
    | succ n ih =>
        intro b hb
        simp only [CriticalTransferData.predecessors] at hb
        rcases Finset.mem_union.mp hb with hb | hb
        · have hprev := ih b hb
          omega
        · rcases Finset.mem_filter.mp hb with ⟨_, hex⟩
          rcases hex with ⟨b₀, hb₀, j, j', hclass₀, hclass, hlt, hflipExists⟩
          rcases hflipExists with ⟨a, a', hflip⟩
          have hprev := ih b₀ hb₀
          have hstep := hammingDist_le_two_of_flipEq a a' hflip
          have htri := hammingDist_triangle X.failure.2.1.1 b₀ b
          omega
  have h := hdist D.geom.r b hb
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

private theorem internalCoords_card_le (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    Fintype.card {a : Fin (T.S.n k) // a ∈ PT.tiling.Icoord i} ≤ (PT.tiling.P i).h := by
  classical
  let h := (PT.tiling.P i).h
  have hhn : h ≤ T.S.n k := by
    have hmax := Tiling.Valid.prefix_internal_length hPT.tiling_valid
    have hhmax : (PT.tiling.P i).h ≤
        Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h :=
      Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h)
        (Finset.mem_univ i)
    omega
  let ix : {a : Fin (T.S.n k) // a ∈ PT.tiling.Icoord i} → Fin h := fun a =>
    ⟨a.1.val - (T.S.n k - h), by
      have hmem : T.S.n k - h ≤ a.1.val := by
        simpa [Tiling.Icoord, topCoordinates, h] using a.2
      omega⟩
  have hinj : Function.Injective ix := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg Fin.val hab
    dsimp [ix] at hv
    have haI : T.S.n k - h ≤ a.1.val := by
      simpa [Tiling.Icoord, topCoordinates, h] using a.2
    have hbI : T.S.n k - h ≤ b.1.val := by
      simpa [Tiling.Icoord, topCoordinates, h] using b.2
    exact (tsub_left_inj haI hbI).mp hv
  simpa using Fintype.card_le_of_injective ix hinj

private theorem cosetCoords_card_le (a : Fin (T.S.n k)) :
    (Finset.univ.filter fun b : Fin (T.S.n k) =>
      D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub).card ≤ D.geom.r := by
  classical
  let C := {b : Fin (T.S.n k) // D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub}
  let code : C → D.geom.Lsub := fun b => ⟨D.geom.ids a - D.geom.ids b.1, b.2⟩
  have hcode : Function.Injective code := by
    intro b c h
    apply Subtype.ext
    apply D.l16_valid.ids_distinct
    have hval : D.geom.ids a - D.geom.ids b.1 = D.geom.ids a - D.geom.ids c.1 :=
      congrArg Subtype.val h
    simpa only [sub_right_inj] using hval
  have hcard : Fintype.card D.geom.Lsub = D.geom.r := by
    simpa using (Fintype.card_congr D.geom.classEnum).symm
  calc
    (Finset.univ.filter fun b : Fin (T.S.n k) =>
        D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub).card = Fintype.card C := by
          simp [C, Fintype.card_subtype]
    _ ≤ Fintype.card D.geom.Lsub := Fintype.card_le_of_injective code hcode
    _ = D.geom.r := hcard

private theorem nearInternalCoords_card_le :
    (Finset.univ.filter fun b : Fin (T.S.n k) => nearInternal (D := D) (X := X) b).card ≤
      (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r := by
  classical
  let i := D.geom.patchOf X.target
  let C := {b : Fin (T.S.n k) // nearInternal (D := D) (X := X) b}
  let I := {t : Fin (T.S.n k) // t ∈ PT.tiling.Icoord i}
  let tOf (b : C) : I := ⟨Classical.choose b.2, (Classical.choose_spec b.2).1⟩
  have hdiff (b : C) : D.geom.ids b.1 - D.geom.ids (tOf b).1 ∈ D.geom.Lsub :=
    (Classical.choose_spec b.2).2
  let code : C → I × D.geom.Lsub := fun b =>
    (tOf b, ⟨D.geom.ids b.1 - D.geom.ids (tOf b).1, hdiff b⟩)
  have hcode : Function.Injective code := by
    intro b c hbc
    apply Subtype.ext
    have ht : (tOf b).1 = (tOf c).1 := congrArg (fun z => z.1.1) hbc
    have hidsDiff : D.geom.ids b.1 - D.geom.ids (tOf b).1 =
        D.geom.ids c.1 - D.geom.ids (tOf c).1 :=
      congrArg (fun z => z.2.1) hbc
    have hids : D.geom.ids b.1 = D.geom.ids c.1 := by
      rw [ht] at hidsDiff
      simpa only [sub_left_inj] using hidsDiff
    exact D.l16_valid.ids_distinct hids
  have hcardL : Fintype.card D.geom.Lsub = D.geom.r := by
    simpa using (Fintype.card_congr D.geom.classEnum).symm
  have hcard : Fintype.card I ≤ (PT.tiling.P i).h := by
    exact internalCoords_card_le hPT i
  calc
    (Finset.univ.filter fun b : Fin (T.S.n k) => nearInternal (D := D) (X := X) b).card =
        Fintype.card C := by simp [C, Fintype.card_subtype]
    _ ≤ Fintype.card (I × D.geom.Lsub) := Fintype.card_le_of_injective code hcode
    _ = Fintype.card I * Fintype.card D.geom.Lsub := by rw [Fintype.card_prod]
    _ ≤ (PT.tiling.P i).h * D.geom.r := Nat.mul_le_mul hcard hcardL.le

theorem block_size (a : Fin (T.S.n k)) :
    (X.criticalCoords.filter (X.sameBlock a)).card ≤
      max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r := by
  classical
  let i := D.geom.patchOf X.target
  let h := (PT.tiling.P i).h
  by_cases ha : nearInternal (D := D) (X := X) a
  · have hsub : X.criticalCoords.filter (X.sameBlock a) ⊆
        Finset.univ.filter (fun b : Fin (T.S.n k) => nearInternal (D := D) (X := X) b) := by
      intro b hb
      have hsame := (Finset.mem_filter.mp hb).2
      change (D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub ∨
        (nearInternal (D := D) (X := X) a ∧ nearInternal (D := D) (X := X) b)) at hsame
      have hnear : nearInternal (D := D) (X := X) b := by
        rcases hsame with hab | ⟨_, hb⟩
        · exact nearInternal_transport (D := D) (X := X) hab ha
        · exact hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnear⟩
    calc
      (X.criticalCoords.filter (X.sameBlock a)).card ≤
          (Finset.univ.filter fun b : Fin (T.S.n k) => nearInternal (D := D) (X := X) b).card :=
        Finset.card_le_card hsub
      _ ≤ h * D.geom.r := nearInternalCoords_card_le (D := D) (X := X)
      _ ≤ max 1 h * D.geom.r := Nat.mul_le_mul_right _ (le_max_right 1 h)
  · have hsub : X.criticalCoords.filter (X.sameBlock a) ⊆
        Finset.univ.filter (fun b : Fin (T.S.n k) =>
          D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub) := by
      intro b hb
      have hsame := (Finset.mem_filter.mp hb).2
      change (D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub ∨
        (nearInternal (D := D) (X := X) a ∧ nearInternal (D := D) (X := X) b)) at hsame
      rcases hsame with hab | ⟨ha', _⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
      · exact (ha ha').elim
    calc
      (X.criticalCoords.filter (X.sameBlock a)).card ≤
          (Finset.univ.filter fun b : Fin (T.S.n k) =>
            D.geom.ids a - D.geom.ids b ∈ D.geom.Lsub).card := Finset.card_le_card hsub
      _ ≤ D.geom.r := cosetCoords_card_le a
      _ ≤ max 1 h * D.geom.r := by
        have h1 : 1 ≤ max 1 h := le_max_left 1 h
        have hr : 0 ≤ D.geom.r := Nat.zero_le _
        nlinarith [Nat.mul_le_mul_right D.geom.r h1]

private theorem directObservation_distance (b : Pos T k) (d : Fin (T.S.n k))
    (hb : b ∈ X.predecessors D.geom.r) (w v : Pos T k)
    (hwd : w = flipPos b d) (hvw : v = w ∨ ∃ j, v = flipPos w j)
    (c : Fin (T.S.n k)) :
    hammingDist v (flipPos X.target c) ≤ 2 * D.geom.r + 4 := by
  let b₀ := X.failure.2.1.1
  let a₀ := X.failure.2.2.2.2
  have htarget : X.target = flipPos b₀ a₀ := rfl
  have hb₀b : hammingDist b₀ b ≤ 2 * D.geom.r := by
    exact (Finset.mem_filter.mp (predecessor_radius (D := D) (X := X) b hb)).2
  have hbb₀ : hammingDist b b₀ ≤ 2 * D.geom.r := by
    rw [hammingDist_comm_lane b b₀]
    exact hb₀b
  have hb₀t : hammingDist b₀ X.target ≤ 1 := by
    rw [htarget]
    exact hammingDist_flip_le_one b₀ a₀
  have httc : hammingDist X.target (flipPos X.target c) ≤ 1 :=
    hammingDist_flip_le_one X.target c
  have hwb : hammingDist w b ≤ 1 := by
    rw [hwd, hammingDist_comm_lane (flipPos b d) b]
    exact hammingDist_flip_le_one b d
  have hvw' : hammingDist v w ≤ 1 := by
    rcases hvw with rfl | ⟨j, rfl⟩
    · simp [hammingDist]
    · rw [hammingDist_comm_lane (flipPos w j) w]
      exact hammingDist_flip_le_one w j
  have hbT : hammingDist b (flipPos X.target c) ≤ 2 * D.geom.r + 2 := by
    have h₁ := hammingDist_triangle b b₀ (flipPos X.target c)
    have h₂ := hammingDist_triangle b₀ X.target (flipPos X.target c)
    omega
  have hwT : hammingDist w (flipPos X.target c) ≤ 2 * D.geom.r + 3 := by
    have h := hammingDist_triangle w b (flipPos X.target c)
    omega
  have hvT := hammingDist_triangle v w (flipPos X.target c)
  omega

private theorem directCell_outer_observation (hmargin :
    (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (w : Pos T k) (hw : w ∈ X.directEven) (c : Fin (T.S.n k))
    (hc : c ∈ X.criticalCoords)
    (hcell : D.geom.cellOf (flipPos X.target c) ∈ D.directCells w) :
    (∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) →
      w a = flipPos X.target c a) ∨
    ∃ j ∈ D.externalEarly w, ∀ a,
      a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) →
        flipPos w j a = flipPos X.target c a := by
  classical
  rcases Finset.mem_biUnion.mp hw with ⟨b, hb, hflipSet⟩
  rcases Finset.mem_image.mp hflipSet with ⟨d, _, hwd⟩
  rcases (by simpa [LateData.directCells] using hcell) with hown | hexternal
  · left
    have hdist := directObservation_distance (D := D) (X := X) b d hb w w hwd.symm
      (Or.inl rfl) c
    have houter := sameCell_outer_eq (D := D) (X := X) w c hc hown.symm hmargin (by
      exact_mod_cast hdist)
    exact houter
  · rcases hexternal with ⟨j, hj, hcellj⟩
    right
    refine ⟨j, hj, ?_⟩
    have hdist := directObservation_distance (D := D) (X := X) b d hb w (flipPos w j)
      hwd.symm (Or.inr ⟨j, rfl⟩) c
    have houter := sameCell_outer_eq (D := D) (X := X) (flipPos w j) c hc hcellj hmargin (by
      exact_mod_cast hdist)
    exact houter

private theorem sameBlock_of_two_directCells (hmargin :
    (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (w : Pos T k) (hw : w ∈ X.directEven \ X.erased)
    (c c' : Fin (T.S.n k)) (hc : c ∈ X.criticalCoords)
    (hc' : c' ∈ X.criticalCoords)
    (hcell : D.geom.cellOf (flipPos X.target c) ∈ D.directCells w)
    (hcell' : D.geom.cellOf (flipPos X.target c') ∈ D.directCells w) :
    X.sameBlock c c' := by
  classical
  let b₀ := X.failure.2.1.1
  let a₀ := X.failure.2.2.2.2
  have htarget : X.target = flipPos b₀ a₀ := rfl
  have hwDirect : w ∈ X.directEven := (Finset.mem_sdiff.mp hw).1
  have hnotErased := notErased_outer_mismatch D X w hw
  have hcNotI : c ∉ PT.tiling.Icoord (D.geom.patchOf X.target) := by
    rcases Finset.mem_filter.mp (Finset.mem_filter.mp hc).1 with ⟨_, ⟨_, h⟩⟩
    exact h
  have hc'NotI : c' ∉ PT.tiling.Icoord (D.geom.patchOf X.target) := by
    rcases Finset.mem_filter.mp (Finset.mem_filter.mp hc').1 with ⟨_, ⟨_, h⟩⟩
    exact h
  rcases Finset.mem_biUnion.mp hwDirect with ⟨b, hb, hflip⟩
  rcases Finset.mem_image.mp hflip with ⟨d, _, hflipEq⟩
  have hwd : w = flipPos b d := hflipEq.symm
  have hbClass := class_some_of_predecessor D X D.geom.r b hb
  have hparity (q : Fin (T.S.n k)) :
      cosetParity D b q = cosetParity D b₀ q :=
    predecessors_cosetParity_eq D X D.geom.r b hb q
  have hb₀Class : ∃ i, D.geom.classOf b₀ = some i := by
    refine ⟨X.failure.1, ?_⟩
    exact (D.encoding.base.class_of_spec b₀ X.failure.1).mp X.failure.2.1.2
  have hcNotA₀ : ¬ sameIdCoset D c a₀ :=
    critical_not_sameIdCoset D X c hc b₀ a₀ htarget hb₀Class
  have hc'NotA₀ : ¬ sameIdCoset D c' a₀ :=
    critical_not_sameIdCoset D X c' hc' b₀ a₀ htarget hb₀Class
  have hcOuter := directCell_outer_observation (D := D) (X := X)
    hmargin w hwDirect c hc hcell
  have hc'Outer := directCell_outer_observation (D := D) (X := X)
    hmargin w hwDirect c' hc' hcell'
  change sameIdCoset D c c' ∨
      (nearInternal (D := D) (X := X) c ∧ nearInternal (D := D) (X := X) c')
  by_cases hcc : sameIdCoset D c c'
  · exact Or.inl hcc
  · have hccne : c ≠ c' := by
      intro heq
      apply hcc
      subst c'
      change D.geom.ids c - D.geom.ids c ∈ D.geom.Lsub
      simp
    rcases hcOuter with hown | ⟨j, hj, houter⟩
    · rcases hc'Outer with hown' | ⟨j', hj', houter'⟩
      · have h₁ := hown c hcNotI
        have h₂ := hown' c hcNotI
        have hf : False := by
          have h₁' : w c = !X.target c := by simpa [flipPos] using h₁
          have h₂' : w c = X.target c := by simpa [flipPos, hccne] using h₂
          have hbad := h₁'.symm.trans h₂'
          cases ht : X.target c <;> simp [ht] at hbad
        exact hf.elim
      · have hj'c' : j' ≠ c' := by
          intro heq
          subst j'
          have htargetOuter := outer_cancel_same_flip (D := D) w X.target c' hc'NotI
            (by simpa using houter')
          exact hnotErased htargetOuter
        have h₁ := hown c' hc'NotI
        have h₂ := houter' c' hc'NotI
        have hf : False := by
          have h₁' : w c' = X.target c' := by simpa [flipPos, hccne.symm] using h₁
          have h₂' : w c' = !X.target c' := by
            simpa [flipPos, hj'c'.symm] using h₂
          have hbad := h₁'.symm.trans h₂'
          cases ht : X.target c' <;> simp [ht] at hbad
        exact hf.elim
    · rcases hc'Outer with hown' | ⟨j', hj', houter'⟩
      · have hjc : j ≠ c := by
          intro heq
          subst j
          have htargetOuter := outer_cancel_same_flip (D := D) w X.target c hcNotI
            (by simpa using houter)
          exact hnotErased htargetOuter
        have h₁ := houter c hcNotI
        have h₂ := hown' c hcNotI
        have hf : False := by
          have h₁' : w c = !X.target c := by
            simpa [flipPos, hjc.symm] using h₁
          have h₂' : w c = X.target c := by
            simpa [flipPos, hccne] using h₂
          have hbad := h₁'.symm.trans h₂'
          cases ht : X.target c <;> simp [ht] at hbad
        exact hf.elim
      · have hjc : j ≠ c := by
          intro heq
          subst j
          have htargetOuter := outer_cancel_same_flip (D := D) w X.target c hcNotI
            (by simpa using houter)
          exact hnotErased htargetOuter
        have hj'c' : j' ≠ c' := by
          intro heq
          subst j'
          have htargetOuter := outer_cancel_same_flip (D := D) w X.target c' hc'NotI
            (by simpa using houter')
          exact hnotErased htargetOuter
        have hj'c : j' = c := by
          by_contra hne
          have h₁ := houter c hcNotI
          have h₂ := houter' c hcNotI
          have h₁' : w c = !X.target c := by
            simpa [flipPos, Ne.symm hjc] using h₁
          have h₂' : w c = X.target c := by
            simpa [flipPos, Ne.symm hne, hccne] using h₂
          have hbad := h₁'.symm.trans h₂'
          cases ht : X.target c <;> simp [ht] at hbad
        have hjc' : j = c' := by
          by_contra hne
          have h₁ := houter c' hc'NotI
          have h₂ := houter' c' hc'NotI
          have h₁' : w c' = X.target c' := by
            simpa [flipPos, Ne.symm hne, hccne.symm] using h₁
          have h₂' : w c' = !X.target c' := by
            simpa [flipPos, Ne.symm hj'c'] using h₂
          have hbad := h₁'.symm.trans h₂'
          cases ht : X.target c' <;> simp [ht] at hbad
        have hnotDC : ¬ sameIdCoset D d c := by
          have h := externalEarly_not_sameIdCoset D b d j' hbClass
            (by simpa [hwd] using hj')
          simpa [hj'c] using h
        have hnotDC' : ¬ sameIdCoset D d c' := by
          have h := externalEarly_not_sameIdCoset D b d j hbClass
            (by simpa [hwd] using hj)
          simpa [hjc'] using h
        have hnotCC' : ¬ sameIdCoset D c' c := by
          intro h
          exact hcc (sameIdCoset_symm D h)
        have hnotA₀C : ¬ sameIdCoset D a₀ c := by
          intro h
          exact hcNotA₀ (sameIdCoset_symm D h)
        have hnotA₀C' : ¬ sameIdCoset D a₀ c' := by
          intro h
          exact hc'NotA₀ (sameIdCoset_symm D h)
        have hselfC : sameIdCoset D c c := by
          change D.geom.ids c - D.geom.ids c ∈ D.geom.Lsub
          simp
        have hselfC' : sameIdCoset D c' c' := by
          change D.geom.ids c' - D.geom.ids c' ∈ D.geom.Lsub
          simp
        have houterC : ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) →
            flipPos w c' a = flipPos X.target c a := by
          simpa [hjc'] using houter
        have houterC' : ∀ a, a ∉ PT.tiling.Icoord (D.geom.patchOf X.target) →
            flipPos w c a = flipPos X.target c' a := by
          simpa [hj'c] using houter'
        have hnearC : nearInternal (D := D) (X := X) c := by
          by_contra hnotNear
          have hpeq := cosetParity_eq_of_outer_no_internal D X
            (flipPos w c') (flipPos X.target c) c houterC hnotNear
          have hsum := cosetParity_doubleFlip_sum D b b₀ d c' a₀ c c (hparity c)
          rw [hwd, htarget] at hpeq
          have hzero :
              cosetParity D (flipPos (flipPos b d) c') c +
                cosetParity D (flipPos (flipPos b₀ a₀) c) c = 0 := by
            rw [hpeq]
            exact zmodTwo_double _
          rw [hzero] at hsum
          simp [hnotDC, hnotCC', hnotA₀C, hselfC] at hsum
        have hnearC' : nearInternal (D := D) (X := X) c' := by
          by_contra hnotNear
          have hpeq := cosetParity_eq_of_outer_no_internal D X
            (flipPos w c) (flipPos X.target c') c' houterC' hnotNear
          have hsum := cosetParity_doubleFlip_sum D b b₀ d c a₀ c' c' (hparity c')
          rw [hwd, htarget] at hpeq
          have hzero :
              cosetParity D (flipPos (flipPos b d) c) c' +
                cosetParity D (flipPos (flipPos b₀ a₀) c') c' = 0 := by
            rw [hpeq]
            exact zmodTwo_double _
          rw [hzero] at hsum
          simp [hnotDC', hcc, hnotA₀C', hselfC'] at hsum
        exact Or.inr ⟨hnearC, hnearC'⟩

theorem one_block_field (hmargin :
    (2 * D.geom.r + 4 : ℕ) ≤ Real.log (T.S.n k : ℝ) ^ 3)
    (w : Pos T k) (hw : w ∈ X.directEven \ X.erased) :
    ∃ a, D.directCells w ∩ X.criticalCells ⊆ X.blockCells a := by
  classical
  let S : Finset (Fin (T.S.n k)) := X.criticalCoords.filter fun a =>
    D.geom.cellOf (flipPos X.target a) ∈ D.directCells w
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha⟩ := hS
    refine ⟨a, ?_⟩
    intro C hC
    rcases Finset.mem_inter.mp hC with ⟨hDirect, hCritical⟩
    rcases Finset.mem_image.mp hCritical with ⟨c, hc, hCeq⟩
    have hcDirect : D.geom.cellOf (flipPos X.target c) ∈ D.directCells w := by
      rw [← hCeq] at hDirect
      exact hDirect
    have hsame := sameBlock_of_two_directCells (D := D) (X := X) hmargin w hw
      a c (Finset.mem_filter.mp ha).1 hc (Finset.mem_filter.mp ha).2 hcDirect
    apply Finset.mem_image.mpr
    exact ⟨c, Finset.mem_filter.mpr ⟨hc, hsame⟩, hCeq⟩
  · have hempty : ∀ C, C ∈ D.directCells w ∩ X.criticalCells → False := by
      intro C hC
      rcases Finset.mem_inter.mp hC with ⟨hDirect, hCritical⟩
      rcases Finset.mem_image.mp hCritical with ⟨c, hc, hCeq⟩
      have hcDirect : D.geom.cellOf (flipPos X.target c) ∈ D.directCells w := by
        rw [← hCeq] at hDirect
        exact hDirect
      exact hS ⟨c, Finset.mem_filter.mpr ⟨hc, hcDirect⟩⟩
    have hn : 0 < T.S.n k := by
      by_contra hpos
      have hzNat : T.S.n k = 0 := by omega
      have hzReal : (T.S.n k : ℝ) = 0 := by exact_mod_cast hzNat
      have hlog : Real.log (T.S.n k : ℝ) = 0 := by rw [hzReal, Real.log_zero]
      rw [hlog] at hmargin
      have hleft : 0 < ((2 * D.geom.r + 4 : ℕ) : ℝ) := by positivity
      have hmargin' : ((2 * D.geom.r + 4 : ℕ) : ℝ) ≤ 0 := by simpa using hmargin
      exact (not_le_of_gt hleft) hmargin'
    refine ⟨⟨0, hn⟩, ?_⟩
    intro C hC
    exact (hempty C hC).elim

private theorem bulkCoords_card_lower (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    T.S.n k - (PT.tiling.P i).ℓ - (PT.tiling.P i).h ≤
      (PT.tiling.bulkCoords i).card := by
  classical
  let cross := PT.tiling.crossingCoords i
  let bulk := PT.tiling.bulkCoords i
  let internal := PT.tiling.Icoord i
  have hlen := Tiling.Valid.prefix_internal_length hPT.tiling_valid
  have hellMax : (PT.tiling.P i).ℓ ≤
      Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ :=
    Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) (Finset.mem_univ i)
  have hhMax : (PT.tiling.P i).h ≤
      Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h :=
    Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h) (Finset.mem_univ i)
  have hlen' : (PT.tiling.P i).ℓ + (PT.tiling.P i).h ≤ T.S.n k := by omega
  have hcover : (Finset.univ : Finset (Fin (T.S.n k))) ⊆ cross ∪ (bulk ∪ internal) := by
    intro a ha
    by_cases hpre : a.val < (PT.tiling.P i).ℓ
    · apply Finset.mem_union.mpr
      left
      simp [cross, Tiling.crossingCoords, hpre]
    · by_cases hI : a ∈ internal
      · apply Finset.mem_union.mpr
        right
        exact Finset.mem_union.mpr (Or.inr hI)
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨by omega, hI⟩⟩
  have hcardCover : T.S.n k ≤ cross.card + bulk.card + internal.card := by
    have h := Finset.card_le_card hcover
    calc
      T.S.n k = (Finset.univ : Finset (Fin (T.S.n k))).card := by simp
      _ ≤ (cross ∪ (bulk ∪ internal)).card := h
      _ ≤ cross.card + (bulk ∪ internal).card := Finset.card_union_le _ _
      _ ≤ cross.card + bulk.card + internal.card := by
        simpa [Nat.add_assoc] using
          Nat.add_le_add_left (Finset.card_union_le bulk internal) cross.card
  have hcross : cross.card ≤ (PT.tiling.P i).ℓ := by
    dsimp [cross, Tiling.crossingCoords]
    rw [Fin.card_filter_val_lt]
    exact Nat.min_le_right _ _
  have hinter : internal.card ≤ (PT.tiling.P i).h := by
    simpa [internal] using internalCoords_card_le hPT i
  have htotal : T.S.n k ≤ bulk.card + (PT.tiling.P i).ℓ + (PT.tiling.P i).h := by
    omega
  calc
    T.S.n k - (PT.tiling.P i).ℓ - (PT.tiling.P i).h =
        T.S.n k - ((PT.tiling.P i).ℓ + (PT.tiling.P i).h) := by omega
    _ ≤ bulk.card := by
      apply (Nat.sub_le_iff_le_add).2
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htotal

private theorem syndromeCosetCoords_card_le :
    (Finset.univ.filter fun b : Fin (T.S.n k) =>
      D.geom.ids b - D.geom.syndrome X.target ∈ D.geom.Lsub).card ≤ D.geom.r := by
  classical
  let C := {b : Fin (T.S.n k) // D.geom.ids b - D.geom.syndrome X.target ∈ D.geom.Lsub}
  let code : C → D.geom.Lsub := fun b => ⟨D.geom.ids b.1 - D.geom.syndrome X.target, b.2⟩
  have hcode : Function.Injective code := by
    intro b c h
    apply Subtype.ext
    apply D.l16_valid.ids_distinct
    have hval : D.geom.ids b.1 - D.geom.syndrome X.target =
        D.geom.ids c.1 - D.geom.syndrome X.target := congrArg Subtype.val h
    simpa only [sub_left_inj] using hval
  have hcard : Fintype.card D.geom.Lsub = D.geom.r := by
    simpa using (Fintype.card_congr D.geom.classEnum).symm
  calc
    (Finset.univ.filter fun b : Fin (T.S.n k) =>
        D.geom.ids b - D.geom.syndrome X.target ∈ D.geom.Lsub).card = Fintype.card C := by
          simp [C, Fintype.card_subtype]
    _ ≤ Fintype.card D.geom.Lsub := Fintype.card_le_of_injective code hcode
    _ = D.geom.r := hcard

private theorem criticalCoords_card_lower_basic (hPT : PT.Valid)
    (hlog : (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3) :
    T.S.n k - (PT.tiling.P (D.geom.patchOf X.target)).ℓ -
        (PT.tiling.P (D.geom.patchOf X.target)).h - D.geom.r - 1 ≤ X.criticalCoords.card := by
  classical
  let i := D.geom.patchOf X.target
  let bulk := PT.tiling.bulkCoords i
  let goodId : Fin (T.S.n k) → Prop := fun a =>
    D.geom.ids a - D.geom.syndrome X.target ∉ D.geom.Lsub
  let keepCell : Fin (T.S.n k) → Prop := fun a =>
    X.omitted ≠ some (D.geom.cellOf (flipPos X.target a))
  let base := bulk.filter goodId
  let badId := bulk.filter fun a => ¬ goodId a
  let removed := base.filter fun a => ¬ keepCell a
  have hbulk := bulkCoords_card_lower hPT i
  have hbaseEq : X.criticalCoords = base.filter keepCell := by
    ext a
    simp [CriticalTransferData.criticalCoords, base, bulk, goodId, keepCell, i,
      Finset.mem_filter, and_assoc, and_left_comm, and_comm]
  have hsplitId : base.card + badId.card = bulk.card := by
    have hs := Finset.card_filter_add_card_filter_not (s := bulk) (p := goodId)
    simpa [base, badId, Nat.add_comm] using hs
  have hbadSubset : badId ⊆
      Finset.univ.filter fun a : Fin (T.S.n k) =>
        D.geom.ids a - D.geom.syndrome X.target ∈ D.geom.Lsub := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [badId, goodId] using (Finset.mem_filter.mp ha).2⟩
  have hbadCard : badId.card ≤ D.geom.r :=
    (Finset.card_le_card hbadSubset).trans syndromeCosetCoords_card_le
  have hsplitCell : X.criticalCoords.card + removed.card = base.card := by
    rw [hbaseEq]
    simpa [removed, Nat.add_comm] using
      (Finset.card_filter_add_card_filter_not (s := base) (p := keepCell))
  have hremoved : removed.card ≤ 1 := by
    cases ho : X.omitted with
    | none => simp [removed, keepCell, ho]
    | some C =>
        apply Finset.card_le_one.mpr
        intro a ha b hb
        have haBase : a ∈ base := (Finset.mem_filter.mp ha).1
        have hbBase : b ∈ base := (Finset.mem_filter.mp hb).1
        have haCell : D.geom.cellOf (flipPos X.target a) = C := by
          have he : X.omitted = some (D.geom.cellOf (flipPos X.target a)) := by
            simpa [keepCell, ne_eq, not_not] using (Finset.mem_filter.mp ha).2
          rw [ho] at he
          exact (Option.some.inj he).symm
        have hbCell : D.geom.cellOf (flipPos X.target b) = C := by
          have he : X.omitted = some (D.geom.cellOf (flipPos X.target b)) := by
            simpa [keepCell, ne_eq, not_not] using (Finset.mem_filter.mp hb).2
          rw [ho] at he
          exact (Option.some.inj he).symm
        have haBulk : a ∈ bulk := (Finset.mem_filter.mp haBase).1
        have hbBulk : b ∈ bulk := (Finset.mem_filter.mp hbBase).1
        exact bulkCoord_eq_of_cellEq (D := D) (X := X) hlog haBulk hbBulk
          (haCell.trans hbCell.symm)
  have hresult : T.S.n k - (PT.tiling.P i).ℓ - (PT.tiling.P i).h - D.geom.r - 1 ≤
      X.criticalCoords.card := by
    have hbulkBound : bulk.card ≤ X.criticalCoords.card + D.geom.r + 1 := by omega
    have htotal : T.S.n k - (PT.tiling.P i).ℓ - (PT.tiling.P i).h ≤
        X.criticalCoords.card + D.geom.r + 1 := hbulk.trans hbulkBound
    have hsub :
        (T.S.n k - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) - (D.geom.r + 1) ≤
          (X.criticalCoords.card + D.geom.r + 1) - (D.geom.r + 1) :=
      Nat.sub_le_sub_right htotal _
    have hright :
        (X.criticalCoords.card + D.geom.r + 1) - (D.geom.r + 1) = X.criticalCoords.card := by omega
    have hleft :
        T.S.n k - (PT.tiling.P i).ℓ - (PT.tiling.P i).h - D.geom.r - 1 =
          (T.S.n k - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) - (D.geom.r + 1) := by omega
    calc
      T.S.n k - (PT.tiling.P i).ℓ - (PT.tiling.P i).h - D.geom.r - 1 =
          (T.S.n k - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) - (D.geom.r + 1) := hleft
      _ ≤ X.criticalCoords.card := by simpa [hright] using hsub
  simpa [i] using hresult

private theorem twice_rpow_five_hundredths_le_self {L : ℝ} (hL : 4 ≤ L) :
    2 * Real.rpow L (1 / 20 : ℝ) ≤ L := by
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hsqrtSq : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt (by positivity)
  have hsqrt : 2 ≤ Real.sqrt L := by nlinarith [hsqrtSq, Real.sqrt_nonneg L]
  have hpow : Real.rpow L (1 / 20 : ℝ) ≤ Real.rpow L (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
  calc
    2 * Real.rpow L (1 / 20 : ℝ) ≤ 2 * Real.sqrt L := by
      rw [Real.sqrt_eq_rpow]
      exact mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ L := by nlinarith [hsqrtSq, hsqrt]

theorem critical_count_field {κ : CConsts} (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ X : CriticalTransferData D,
        (T.S.n k : ℝ) - (κ.KB + 4 * κ.A0 + 10) * Real.log (T.S.n k) ≤
          X.criticalCoords.card := by
  have hKB0 : 0 ≤ κ.KB := by
    have hR : 0 ≤ (κ.R : ℝ) := Nat.cast_nonneg _
    exact le_trans (by positivity) hκ.KB_big
  have hA00 : 0 ≤ κ.A0 := by
    have hR : 0 ≤ (κ.R : ℝ) := Nat.cast_nonneg _
    exact le_trans (by positivity) hκ.A0_big
  have hCoeff : 0 < κ.KB + 4 * κ.A0 + 10 := by linarith
  have hnReal : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlogT : Tendsto (fun k => Real.log (T.S.n k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnReal
  have hlogEventually : ∀ᶠ k in atTop, 4 ≤ Real.log (T.S.n k : ℝ) :=
    hlogT.eventually_ge_atTop 4
  have hlogOverN : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp
        tendsto_natCast_atTop_atTop)
  have hcoeffRatio : Tendsto
      (fun k => (κ.KB + 4 * κ.A0 + 10) * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ))
      atTop (nhds 0) := by
    simpa [mul_div_assoc] using
      (tendsto_const_nhds.mul (hlogOverN.comp T.S.n_tendsto))
  have hsmallLossEventually : ∀ᶠ k in atTop,
      (κ.KB + 4 * κ.A0 + 10) * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) < 1 :=
    hcoeffRatio.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hnEventually : ∀ᶠ k in atTop, 1 ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 1
  filter_upwards [hlogEventually, hsmallLossEventually, hnEventually] with k hL hsmallLoss hNat
  intro PT hPT D hD X
  let n : ℝ := (T.S.n k : ℝ)
  let L : ℝ := Real.log n
  let i := D.geom.patchOf X.target
  have hN : 1 ≤ n := by
    simpa [n] using (show (1 : ℝ) ≤ (T.S.n k : ℝ) by exact_mod_cast hNat)
  have hnpos : 0 < n := by linarith
  have hL4 : 4 ≤ L := by simpa [L, n] using hL
  have hLpos : 0 < L := by linarith
  have hlogCube : (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3 := by
    have hp : (4 : ℝ) ^ 3 ≤ Real.log (T.S.n k : ℝ) ^ 3 := by gcongr
    norm_num at hp
    linarith
  have hbasic := criticalCoords_card_lower_basic (D := D) (X := X) hPT hlogCube
  have hKB : 0 ≤ κ.KB := hKB0
  have hA0 : 0 ≤ κ.A0 := hA00
  have haPos : 0 < κ.a := by
    rw [hκ.a_eq]
    exact div_pos hκ.θ_rng.1 (by norm_num)
  have hGainNonneg : 0 ≤ PT.tiling.gain i := by
    cases hm : PT.tiling.mode <;> simp [Tiling.gain, hm] <;> positivity
  have huPos : 0 < κ.u := by
    have hu := hκ.u_rng.2
    nlinarith [sq_nonneg (κ.L : ℝ)]
  have huNat : 0 < κ.u := by exact_mod_cast huPos
  have huOneNat : 1 ≤ κ.u := Nat.succ_le_iff.mpr huNat
  have huOne : 1 ≤ (κ.u : ℝ) := by exact_mod_cast huOneNat
  have hden : 1 ≤ 1000 * (κ.u : ℝ) := by nlinarith
  have hdiv : PT.tiling.gain i / (1000 * (κ.u : ℝ)) ≤ PT.tiling.gain i := by
    apply (div_le_iff₀ (by positivity : 0 < 1000 * (κ.u : ℝ))).2
    have hprod := mul_nonneg hGainNonneg (sub_nonneg.mpr hden)
    nlinarith
  have hGainUpper : PT.tiling.gain i ≤ κ.KB * L := by
    simpa [L, n] using D.l16_valid.gain_upper i
  have hEll : ((PT.tiling.P i).ℓ : ℝ) ≤ κ.KB * L := by
    by_cases hbounded : PT.tiling.mode = .bounded
    · obtain ⟨_, hall⟩ := hPT.tiling_valid.bounded_data hbounded
      obtain ⟨hell, _, _, _, _⟩ := hall i
      have hellZero : ((PT.tiling.P i).ℓ : ℝ) = 0 := by exact_mod_cast hell
      rw [hellZero]
      exact mul_nonneg hKB (le_of_lt hLpos)
    · rcases (hPT.tiling_valid.allocation_bounds i).2 with hb | ⟨hell, _⟩
      · exact (hbounded hb).elim
      · exact hell.trans (hdiv.trans hGainUpper)
  have hCb : 100 < κ.Cb := by
    have hratio : 0 < 100 * κ.aC / κ.aB :=
      div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
    linarith [hκ.Cb_big]
  have hMlo : 0 < (κ.Mlo : ℝ) := by linarith [hκ.Mlo_big, hCb]
  have hcm : κ.cq * (κ.Mlo : ℝ) < 1 / 20 := by
    have hden' : 0 < 20 * (κ.Mlo : ℝ) := by positivity
    have hmul := (lt_div_iff₀ hden').mp hκ.cq_rng.2
    nlinarith
  have hHeight : ((PT.tiling.P i).h : ℝ) ≤ L := by
    cases hm : PT.tiling.mode with
    | bounded =>
        obtain ⟨_, hall⟩ := hPT.tiling_valid.bounded_data hm
        obtain ⟨_, hheight, _, _, _⟩ := hall i
        simpa [hheight] using (show (0 : ℝ) ≤ L from le_of_lt hLpos)
    | lowDirect =>
        obtain ⟨_, _, _, _, hheight, _, _⟩ := hPT.tiling_valid.direct_data (Or.inl hm) i
        simpa [hheight] using (show (0 : ℝ) ≤ L from le_of_lt hLpos)
    | lowCluster =>
        obtain ⟨_, _, _, _, _, _, _, _, hheight, hlowQ, _, _⟩ :=
          hPT.tiling_valid.cluster_data (Or.inl hm) i
        have hq : ((PT.tiling.P i).q : ℝ) ≤ Real.rpow L κ.cq := by
          simpa [L, n] using hlowQ.mp hm
        have hqpow : Real.rpow ((PT.tiling.P i).q : ℝ) (κ.Mlo : ℝ) ≤
            Real.rpow L (κ.cq * (κ.Mlo : ℝ)) := by
          calc
            Real.rpow ((PT.tiling.P i).q : ℝ) (κ.Mlo : ℝ) ≤
                Real.rpow (Real.rpow L κ.cq) (κ.Mlo : ℝ) :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) hq (Nat.cast_nonneg _)
            _ = Real.rpow L (κ.cq * (κ.Mlo : ℝ)) := by
              exact (Real.rpow_mul (le_of_lt hLpos) κ.cq (κ.Mlo : ℝ)).symm
        have hqExp : Real.rpow L (κ.cq * (κ.Mlo : ℝ)) ≤ Real.rpow L (1 / 20 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [hL4]) hcm.le
        have hheightQ : ((PT.tiling.P i).h : ℝ) <
            2 * Real.rpow ((PT.tiling.P i).q : ℝ) (κ.Mlo : ℝ) := by
          simpa [hm] using hheight
        have hheightL : ((PT.tiling.P i).h : ℝ) < 2 * Real.rpow L (1 / 20 : ℝ) := by
          calc
            ((PT.tiling.P i).h : ℝ) <
                2 * Real.rpow ((PT.tiling.P i).q : ℝ) (κ.Mlo : ℝ) := hheightQ
            _ ≤ 2 * Real.rpow L (1 / 20 : ℝ) :=
              mul_le_mul_of_nonneg_left (hqpow.trans hqExp) (by norm_num)
        exact hheightL.le.trans (twice_rpow_five_hundredths_le_self hL4)
    | highDirect =>
        have hlow := D.low_mode
        simp [Mode.isLow, hm] at hlow
    | highSmall =>
        have hlow := D.low_mode
        simp [Mode.isLow, hm] at hlow
    | highLarge =>
        have hlow := D.low_mode
        simp [Mode.isLow, hm] at hlow
  have hlog2 : 1 / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hr : (D.geom.r : ℝ) ≤ 4 * κ.A0 * L := by
    have hscale : (D.geom.r : ℝ) ≤ 2 * ((D.geom.r : ℝ) * Real.log 2) := by
      calc
        (D.geom.r : ℝ) = (D.geom.r : ℝ) * 1 := by ring
        _ ≤ (D.geom.r : ℝ) * (2 * Real.log 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith [hlog2]) (Nat.cast_nonneg _)
        _ = 2 * ((D.geom.r : ℝ) * Real.log 2) := by ring
    nlinarith [D.l16_valid.r_upper, hscale, hA0, hLpos]
  have hLoss : ((PT.tiling.P i).ℓ : ℝ) + (PT.tiling.P i).h + D.geom.r + 1 ≤
      (κ.KB + 4 * κ.A0 + 10) * L := by
    have hOne : 1 ≤ L := by linarith
    have hsum : ((PT.tiling.P i).ℓ : ℝ) + (PT.tiling.P i).h + D.geom.r + 1 ≤
        κ.KB * L + L + 4 * κ.A0 * L + 1 := by
      linarith [hEll, hHeight, hr]
    nlinarith [hsum, hOne, hKB, hA0]
  have hCLt : (κ.KB + 4 * κ.A0 + 10) * L < n := by
    have hh := (div_lt_iff₀ hnpos).mp (by simpa [L, n] using hsmallLoss)
    simpa [n, L] using hh
  let lossN : ℕ := (PT.tiling.P i).ℓ + (PT.tiling.P i).h + D.geom.r + 1
  have hLossCast : (lossN : ℝ) ≤ (κ.KB + 4 * κ.A0 + 10) * L := by
    simpa [lossN, Nat.cast_add] using hLoss
  have hLossNat : lossN ≤ T.S.n k := by
    have hlt : (lossN : ℝ) < (T.S.n k : ℝ) := lt_of_le_of_lt hLossCast hCLt
    have hltNat : lossN < T.S.n k := by exact_mod_cast hlt
    exact hltNat.le
  have hbasicNat : T.S.n k - lossN ≤ X.criticalCoords.card := by
    have heq : T.S.n k - (PT.tiling.P (D.geom.patchOf X.target)).ℓ -
        (PT.tiling.P (D.geom.patchOf X.target)).h - D.geom.r - 1 = T.S.n k - lossN := by
      dsimp [lossN, i]
      omega
    rw [heq] at hbasic
    exact hbasic
  have hbasicR : (T.S.n k : ℝ) - (lossN : ℝ) ≤ X.criticalCoords.card := by
    have hcast : ((T.S.n k - lossN : ℕ) : ℝ) =
        (T.S.n k : ℝ) - (lossN : ℝ) := by rw [Nat.cast_sub hLossNat]
    rw [← hcast]
    exact_mod_cast hbasicNat
  have hleft : (T.S.n k : ℝ) - (κ.KB + 4 * κ.A0 + 10) * L ≤
      (T.S.n k : ℝ) - (lossN : ℝ) := by
    linarith [hLossCast]
  exact hleft.trans hbasicR

theorem replyRange_card_le_codeCard (P : TransferProtocol X) (seed : P.Seed)
    [DecidableEq P.Reply]
    (a : Fin (T.S.n k)) (fixed : X.Raw) (hlog : (2 : ℝ) < Real.log (T.S.n k : ℝ) ^ 3) :
    (((Finset.univ : Finset X.Raw).filter
      (fun s => ∀ C, C ∉ X.blockCells a → s C = fixed C)).image
      (fun s => P.replies seed s P.steps)).card ≤
      (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ + 1) *
        (Fintype.card (Fin P.steps × P.Reply) + 1) ^ ⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ := by
  classical
  let S : Finset X.Raw := Finset.univ.filter fun s => ∀ C, C ∉ X.blockCells a → s C = fixed C
  let f : X.Raw → List P.Reply := fun s => P.replies seed s P.steps
  let g : X.Raw → List (Fin P.steps × P.Reply) := fun s => activeTrace P seed a s
  let e : X.Raw → Fin (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ + 1) ×
      (Fin (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊) → Option (Fin P.steps × P.Reply)) :=
    fun s => activeTraceCode P seed a s
  have hout (s : X.Raw) (hs : s ∈ S) :
      ∀ C, C ∉ X.blockCells a → s C = fixed C := (Finset.mem_filter.mp hs).2
  have hfg : ∀ s, s ∈ S → ∀ s', s' ∈ S → g s = g s' → f s = f s' := by
    intro s hs s' hs' htrace
    have hss' : ∀ C, C ∉ X.blockCells a → s C = s' C := by
      intro C hC
      calc
        s C = fixed C := hout s hs C hC
        _ = s' C := (hout s' hs' C hC).symm
    exact replies_eq_of_activeTrace_eq P seed a hlog hss' htrace
  have hge : ∀ s, s ∈ S → ∀ s', s' ∈ S → e s = e s' → g s = g s' := by
    intro s hs s' hs' he
    exact activeTrace_eq_of_code_eq P seed a s s' he
  calc
    (S.image f).card ≤ (S.image g).card := card_image_le_card_of_factor S f g hfg
    _ ≤ (S.image e).card := card_image_le_card_of_factor S g e hge
    _ ≤ Fintype.card
          ((Fin (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ + 1)) ×
            (Fin (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊) → Option (Fin P.steps × P.Reply))) :=
      Finset.card_le_univ _
    _ = (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ + 1) *
          (Fintype.card (Fin P.steps × P.Reply) + 1) ^ ⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ := by simp

set_option maxHeartbeats 400000 in
theorem protocol_code_exponential_bound (P : TransferProtocol X)
    (hN : 1 ≤ (T.S.n k : ℝ))
    (hL : 2 ≤ Real.log (T.S.n k : ℝ))
    (hsmall : Real.log (T.S.n k : ℝ) ^ 28 /
        Real.rpow (T.S.n k : ℝ) (3 / 20 : ℝ) < 1 / 1000) :
    (((⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ + 1 : ℕ) : ℝ) *
      ((Fintype.card (Fin P.steps × P.Reply) + 1 : ℕ) : ℝ) ^
        ⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊) ≤
      Real.exp (Real.rpow (T.S.n k : ℝ) (2 / 5 : ℝ)) := by
  let n : ℝ := (T.S.n k : ℝ)
  let L : ℝ := Real.log n
  let M : ℕ := ⌈L ^ 20⌉₊
  let m : ℝ := (sketchLength T k : ℝ)
  let A : ℝ := L ^ 8 * m
  let B : ℝ := Real.rpow n (1 / 4 : ℝ) * L ^ 8
  let steps : ℝ := (P.steps : ℝ)
  let replies : ℝ := (Fintype.card P.Reply : ℝ)
  let alph : ℝ := (Fintype.card (Fin P.steps × P.Reply) : ℝ)
  have hn : 1 ≤ n := by simpa [n] using hN
  have hL' : 2 ≤ L := by simpa [L, n] using hL
  have hnpos : 0 < n := by linarith
  have hLpos : 0 < L := by linarith
  have hLnonneg : 0 ≤ L := le_of_lt hLpos
  have hLone : 1 ≤ L := by linarith
  have hnquarter : 1 ≤ Real.rpow n (1 / 4 : ℝ) := by
    exact Real.one_le_rpow hn (by norm_num)
  have hsyntaxTwo : n ^ (2 / 5 : ℝ) = Real.rpow n (2 / 5 : ℝ) := rfl
  have hL20 : 1 ≤ L ^ 20 := one_le_pow₀ hLone
  have hL8 : L ≤ L ^ 8 := by
    calc
      L = L * 1 := by ring
      _ ≤ L * L ^ 7 := mul_le_mul_of_nonneg_left (one_le_pow₀ hLone) hLnonneg
      _ = L ^ 8 := by ring
  have hMceil : (M : ℝ) < L ^ 20 + 1 := by
    dsimp [M]
    exact Nat.ceil_lt_add_one (by positivity)
  have hMbound : (M : ℝ) ≤ 2 * L ^ 20 := by
    have hM := hMceil.le
    dsimp [M] at hM ⊢
    linarith
  have hMplus : (M : ℝ) + 1 ≤ 3 * L ^ 20 := by
    have hM := hMceil
    dsimp [M] at hM ⊢
    nlinarith [hL20]
  have hmUpper : m ≤ n ^ (1 / 4 : ℝ) + 1 := by
    dsimp [m, sketchLength, n]
    have hceil := (Nat.ceil_lt_add_one
      (show (0 : ℝ) ≤ (T.S.n k : ℝ) ^ (0.25 : ℝ) by positivity)).le
    simpa only [show (0.25 : ℝ) = 1 / 4 by norm_num] using hceil
  have hmLower : n ^ (1 / 4 : ℝ) ≤ m := by
    dsimp [m, sketchLength, n]
    simpa only [show (0.25 : ℝ) = 1 / 4 by norm_num] using
      (Nat.le_ceil ((T.S.n k : ℝ) ^ (0.25 : ℝ)))
  have hsyntax : n ^ (1 / 4 : ℝ) = Real.rpow n (1 / 4 : ℝ) := rfl
  have hmUpperR : m ≤ Real.rpow n (1 / 4 : ℝ) + 1 := by
    simpa [hsyntax] using hmUpper
  have hmTwo : m ≤ 2 * Real.rpow n (1 / 4 : ℝ) := by
    linarith [hmUpperR, hnquarter]
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hBgeL : L ≤ B := by
    dsimp [B]
    calc
      L ≤ L ^ 8 := hL8
      _ ≤ Real.rpow n (1 / 4 : ℝ) * L ^ 8 :=
        by simpa using mul_le_mul_of_nonneg_right hnquarter (by positivity)
  have hBge1 : 1 ≤ B := by linarith [hBgeL, hLone]
  have hBupper : B ≤ Real.rpow n (1 / 4 : ℝ) * L ^ 28 := by
    dsimp [B]
    have hpow : L ^ 8 ≤ L ^ 28 := by
      calc
        L ^ 8 = L ^ 8 * 1 := by ring
        _ ≤ L ^ 8 * L ^ 20 := mul_le_mul_of_nonneg_left hL20 (by positivity)
        _ = L ^ 28 := by ring
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hLtoCode : L ≤ Real.rpow n (1 / 4 : ℝ) * L ^ 28 := by
    calc
      L ≤ L ^ 28 := by
        calc
          L ≤ L ^ 8 := hL8
          _ ≤ L ^ 28 := by
            calc
              L ^ 8 = L ^ 8 * 1 := by ring
              _ ≤ L ^ 8 * L ^ 20 := mul_le_mul_of_nonneg_left hL20 (by positivity)
              _ = L ^ 28 := by ring
      _ ≤ Real.rpow n (1 / 4 : ℝ) * L ^ 28 :=
        by simpa using mul_le_mul_of_nonneg_right hnquarter (by positivity)
  have hAupper : A ≤ 2 * B := by
    dsimp [A, B]
    calc
      L ^ 8 * m ≤ L ^ 8 * (2 * Real.rpow n (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmTwo (by positivity)
      _ = 2 * (Real.rpow n (1 / 4 : ℝ) * L ^ 8) := by ring
  have hreplies : replies ≤ 1 + Real.exp A := by
    simpa [replies, A, L, n] using P.reply_card
  have hRplus : replies + 1 ≤ 3 * Real.exp A := by
    calc
      replies + 1 ≤ 2 + Real.exp A := by linarith [hreplies]
      _ ≤ 3 * Real.exp A := by
        have hexp : 1 ≤ Real.exp A := Real.one_le_exp_iff.mpr (by positivity)
        nlinarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogL : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hlogReply : Real.log (replies + 1) ≤ A + 2 := by
    calc
      Real.log (replies + 1) ≤ Real.log (3 * Real.exp A) :=
        Real.log_le_log (by positivity) hRplus
      _ = Real.log 3 + A := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos A)), Real.log_exp]
      _ ≤ A + 2 := by linarith
  have hstepsBound : steps ≤ n * L ^ 20 := by
    simpa [steps, n, L] using P.steps_bound
  have hstepPlus : steps + 1 ≤ 2 * n * L ^ 20 := by
    have hnL : 1 ≤ n * L ^ 20 := by nlinarith [hn, hL20]
    nlinarith [hstepsBound, hnL]
  have hlogStep : Real.log (steps + 1) ≤ 22 * L := by
    calc
      Real.log (steps + 1) ≤ Real.log (2 * n * L ^ 20) :=
        Real.log_le_log (by positivity) hstepPlus
      _ = Real.log 2 + L + 20 * Real.log L := by
        calc
          Real.log (2 * n * L ^ 20) = Real.log (2 * n) + Real.log (L ^ 20) :=
            Real.log_mul (ne_of_gt (mul_pos (by norm_num) hnpos)) (by positivity)
          _ = (Real.log 2 + Real.log n) + 20 * Real.log L := by
            rw [Real.log_mul (by norm_num) (ne_of_gt hnpos), Real.log_pow]
            norm_num
          _ = Real.log 2 + L + 20 * Real.log L := by
            simp only [L]
      _ ≤ 22 * L := by nlinarith [hlog2, hlogL, hLone]
  have halph : alph = steps * replies := by
    simp [alph, steps, replies]
  have halphPlus : alph + 1 ≤ (steps + 1) * (replies + 1) := by
    rw [halph]
    have hstepsNonneg : 0 ≤ steps := by dsimp [steps]; positivity
    have hreplyNonneg : 0 ≤ replies := by dsimp [replies]; positivity
    nlinarith [mul_nonneg hstepsNonneg hreplyNonneg]
  have hlogAlph : Real.log (alph + 1) ≤ Real.log (steps + 1) + Real.log (replies + 1) := by
    calc
      Real.log (alph + 1) ≤ Real.log ((steps + 1) * (replies + 1)) :=
        Real.log_le_log (by positivity) halphPlus
      _ = Real.log (steps + 1) + Real.log (replies + 1) := by
        rw [Real.log_mul (by positivity) (by positivity)]
  have hlogAlphBound : Real.log (alph + 1) ≤ 26 * B := by
    calc
      Real.log (alph + 1) ≤ 22 * L + (A + 2) := by
        exact le_trans hlogAlph (add_le_add hlogStep hlogReply)
      _ ≤ 26 * B := by nlinarith [hAupper, hBgeL, hBge1]
  have hcardAlphaNonneg : 0 ≤ alph := by dsimp [alph]; positivity
  have hlogAlphaNonneg : 0 ≤ Real.log (alph + 1) :=
    Real.log_nonneg (by linarith)
  have hterm : (M : ℝ) * Real.log (alph + 1) ≤ 52 * Real.rpow n (1 / 4 : ℝ) * L ^ 28 := by
    calc
      (M : ℝ) * Real.log (alph + 1) ≤ (2 * L ^ 20) * (26 * B) :=
        mul_le_mul hMbound hlogAlphBound hlogAlphaNonneg (by positivity)
      _ = 52 * Real.rpow n (1 / 4 : ℝ) * L ^ 28 := by dsimp [B]; ring
  have hlogM : Real.log ((M : ℝ) + 1) ≤ 22 * L := by
    calc
      Real.log ((M : ℝ) + 1) ≤ Real.log (3 * L ^ 20) :=
        Real.log_le_log (by positivity) hMplus
      _ = Real.log 3 + 20 * Real.log L := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        norm_num
      _ ≤ 22 * L := by nlinarith [hlog3, hlogL, hLone]
  have hlogCode :
      Real.log (((M : ℝ) + 1) * (alph + 1) ^ M) ≤
        200 * Real.rpow n (1 / 4 : ℝ) * L ^ 28 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    calc
      Real.log ((M : ℝ) + 1) + (M : ℝ) * Real.log (alph + 1) ≤
          22 * L + 52 * Real.rpow n (1 / 4 : ℝ) * L ^ 28 :=
        add_le_add hlogM hterm
      _ ≤ 200 * Real.rpow n (1 / 4 : ℝ) * L ^ 28 := by
        have hLcode := hLtoCode
        nlinarith
  have hsmall' : L ^ 28 < (1 / 1000 : ℝ) * Real.rpow n (3 / 20 : ℝ) := by
    have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos hnpos (3 / 20 : ℝ))).mp
      (by simpa [L, n] using hsmall)
    simpa [L, n] using hh
  have hcodeExp : 200 * Real.rpow n (1 / 4 : ℝ) * L ^ 28 ≤
      Real.rpow n (2 / 5 : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hsmall' (by positivity :
      0 < 200 * Real.rpow n (1 / 4 : ℝ))
    have hpow : Real.rpow n (1 / 4 : ℝ) * Real.rpow n (3 / 20 : ℝ) =
        Real.rpow n (2 / 5 : ℝ) := by
      calc
        Real.rpow n (1 / 4 : ℝ) * Real.rpow n (3 / 20 : ℝ) =
            Real.rpow n ((1 / 4 : ℝ) + 3 / 20) := (Real.rpow_add hnpos _ _).symm
        _ = Real.rpow n (2 / 5 : ℝ) := by congr 1 <;> norm_num
    have hcodeExpLt : 200 * Real.rpow n (1 / 4 : ℝ) * L ^ 28 <
          (1 / 5 : ℝ) * Real.rpow n (1 / 4 : ℝ) * Real.rpow n (3 / 20 : ℝ) := by
      calc
        200 * Real.rpow n (1 / 4 : ℝ) * L ^ 28 <
            200 * Real.rpow n (1 / 4 : ℝ) * ((1 / 1000 : ℝ) * Real.rpow n (3 / 20 : ℝ)) := hmul
        _ = (1 / 5 : ℝ) * Real.rpow n (1 / 4 : ℝ) * Real.rpow n (3 / 20 : ℝ) := by ring
    have hcodeExpSmall : 200 * Real.rpow n (1 / 4 : ℝ) * L ^ 28 <
        (1 / 5 : ℝ) * Real.rpow n (2 / 5 : ℝ) := by
      calc
        _ < (1 / 5 : ℝ) * Real.rpow n (1 / 4 : ℝ) * Real.rpow n (3 / 20 : ℝ) := hcodeExpLt
        _ = (1 / 5 : ℝ) * Real.rpow n (2 / 5 : ℝ) := by
          calc
            (1 / 5 : ℝ) * Real.rpow n (1 / 4 : ℝ) * Real.rpow n (3 / 20 : ℝ) =
                (1 / 5 : ℝ) * (Real.rpow n (1 / 4 : ℝ) * Real.rpow n (3 / 20 : ℝ)) := by ring
            _ = (1 / 5 : ℝ) * Real.rpow n (2 / 5 : ℝ) := by rw [hpow]
    exact hcodeExpSmall.le.trans <| by
      simpa only [one_mul, hsyntaxTwo] using
        (mul_le_mul_of_nonneg_right (by norm_num : (1 / 5 : ℝ) ≤ 1)
          (Real.rpow_nonneg (le_of_lt hnpos) (2 / 5 : ℝ)))
  have hcodePos : 0 < ((M : ℝ) + 1) * (alph + 1) ^ M := by positivity
  have hcodeBound : ((M : ℝ) + 1) * (alph + 1) ^ M ≤ Real.exp (Real.rpow n (2 / 5 : ℝ)) := by
    calc
      ((M : ℝ) + 1) * (alph + 1) ^ M =
          Real.exp (Real.log (((M : ℝ) + 1) * (alph + 1) ^ M)) :=
            (Real.exp_log hcodePos).symm
      _ ≤ Real.exp (Real.rpow n (2 / 5 : ℝ)) :=
            Real.exp_le_exp.mpr (le_trans hlogCode hcodeExp)
  simpa [M, alph, n, L] using hcodeBound

end HypercubeRamsey.S18.Lane_q_s18_n2
