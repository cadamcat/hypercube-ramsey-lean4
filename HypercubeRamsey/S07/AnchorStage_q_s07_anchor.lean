import HypercubeRamsey.S07.TagStage
import HypercubeRamsey.S03.GatedPosterior
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.S07

open Classical Filter Real OAI.HypercubeRamsey
open scoped Topology
open scoped BigOperators

private theorem anchor_pi_weight_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (ω : ∀ i, Ω i) :
    (∏ i, (P i).w (ω i)) =
      (∏ i : {i // i ∈ s}, (P i.1).w (ω i.1)) *
      (∏ i : {i // i ∉ s}, (P i.1).w (ω i.1)) := by
  classical
  let f : ι → ℝ := fun i => (P i).w (ω i)
  let t : Finset ι := Finset.univ.filter (fun i => i ∉ s)
  have hs : (∏ i : {i // i ∈ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∈ s, f i := by
    rw [Finset.univ_eq_attach]
    simpa [f] using Finset.prod_attach s f
  let ecomp : {i // i ∉ s} ≃ {i // i ∈ t} := {
    toFun := fun i => ⟨i.1, by simp [t, i.2]⟩
    invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl
  }
  have hnot : (∏ i : {i // i ∉ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∉ s, f i := by
    calc
      (∏ i : {i // i ∉ s}, f i.1) = ∏ i : {i // i ∈ t}, f i.1 :=
        Fintype.prod_equiv ecomp _ _ (by intro i; rfl)
      _ = ∏ i ∈ t.attach, f i.1 := by rw [Finset.univ_eq_attach]
      _ = ∏ i ∈ t, f i := Finset.prod_attach t f
      _ = ∏ i ∈ Finset.univ with i ∉ s, f i := by simp [t]
  calc
    (∏ i, f i) =
        (∏ i ∈ Finset.univ with i ∈ s, f i) *
          (∏ i ∈ Finset.univ with i ∉ s, f i) :=
      (Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun i : ι => i ∈ s) f).symm
    _ = (∏ i : {i // i ∈ s}, f i.1) *
          (∏ i : {i // i ∉ s}, f i.1) := by rw [← hs, ← hnot]

theorem anchor_pi_expect_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ a : (∀ i : {i // i ∈ s}, Ω i.1),
        ∑ b : (∀ i : {i // i ∉ s}, Ω i.1),
          (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a *
            (FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
            f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b)) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  change (∑ ω, (∏ i, (P i).w (ω i)) * f ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  rw [anchor_pi_weight_split P s (e.symm (a, b))]
  change ((∏ i : {i // i ∈ s}, (P i.1).w (e.symm (a, b) i.1)) *
      (∏ i : {i // i ∉ s}, (P i.1).w (e.symm (a, b) i.1))) * f (e.symm (a, b)) = _
  have hleft : ∀ i : {i // i ∈ s}, e.symm (a, b) i.1 = a i := by
    intro i
    simp [e, Equiv.piEquivPiSubtypeProd]
  have hright : ∀ i : {i // i ∉ s}, e.symm (a, b) i.1 = b i := by
    intro i
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2]
  simp_rw [hleft, hright]
  rfl

theorem pi_pr_le_of_cond_coordinate
    {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : V → FinProb Ω) (i : V) (Bad : (V → Ω) → Prop) (B : ℝ)
    (hcond : ∀ ω, ∑ z, (P i).w z *
      (if Bad (Function.update ω i z) then 1 else 0) ≤ B) :
    (FinProb.pi P).pr Bad ≤ B := by
  classical
  let s : Finset V := {i}
  let I := {v : V // v ∈ s}
  let O := {v : V // v ∉ s}
  letI : Unique I := {
    default := ⟨i, by simp [s]⟩
    uniq := by
      intro v
      apply Subtype.ext
      have hv' : v.1 ∈ ({i} : Finset V) := by simpa [s] using v.2
      exact Finset.mem_singleton.mp hv'
  }
  have hdefault : (default : I).1 = i := by
    exact Finset.mem_singleton.mp (by simpa [s] using (default : I).property)
  let eOne : (I → Ω) ≃ Ω := Equiv.piUnique (fun _ : I => Ω)
  let ePi := Equiv.piEquivPiSubtypeProd (fun v : V => v ∈ s) (fun _ => Ω)
  let Pone : FinProb (I → Ω) := FinProb.pi (fun v : I => P v.1)
  let Pout : FinProb (O → Ω) := FinProb.pi (fun v : O => P v.1)
  have hnonempty : Nonempty Ω := by
    by_contra h
    haveI : IsEmpty Ω := ⟨fun z => h ⟨z⟩⟩
    have hsum : (∑ z, (P i).w z) = 0 := by simp
    rw [(P i).sum_eq_one] at hsum
    norm_num at hsum
  let z₀ : Ω := Classical.choice hnonempty
  let base (b : O → Ω) : V → Ω := ePi.symm (eOne.symm z₀, b)
  have hbaseUpdate (b : O → Ω) (z : Ω) :
      ePi.symm (eOne.symm z, b) = Function.update (base b) i z := by
    funext v
    by_cases hvi : v = i
    · subst v
      simp [base, ePi, eOne, Equiv.piEquivPiSubtypeProd, s]
    · have hvout : v ∉ s := by simp [s, hvi]
      simp [base, ePi, eOne, Equiv.piEquivPiSubtypeProd, s, hvi, hvout]
  have hOneWeight (a : I → Ω) :
      Pone.w a = (P i).w (eOne a) := by
    have hweight := congrArg (fun v => (P v).w (a default)) hdefault
    calc
      Pone.w a = (P (default : I).1).w (a default) := by
        simp [Pone, FinProb.pi, Equiv.piUnique]
      _ = (P i).w (a default) := hweight
      _ = (P i).w (eOne a) := by simp [eOne, Equiv.piUnique]
  have hprAsExpect : (FinProb.pi P).pr Bad =
      (FinProb.pi P).expect (fun ω => if Bad ω then 1 else 0) := by
    simp [FinProb.pr, FinProb.expect, mul_ite]
  have hsplit : (FinProb.pi P).expect (fun ω => if Bad ω then 1 else 0) =
      ∑ a : (I → Ω), ∑ b : (O → Ω),
        Pone.w a * Pout.w b *
          (if Bad (ePi.symm (a, b)) then 1 else 0) := by
    simpa [Pone, Pout, I, O, ePi, s] using
      anchor_pi_expect_split P s (fun ω => if Bad ω then 1 else 0)
  calc
    (FinProb.pi P).pr Bad =
        ∑ a : (I → Ω), ∑ b : (O → Ω),
          Pone.w a * Pout.w b *
            (if Bad (ePi.symm (a, b)) then 1 else 0) := by
      rw [hprAsExpect, hsplit]
    _ = ∑ z : Ω, ∑ b : (O → Ω),
          (P i).w z * Pout.w b *
            (if Bad (ePi.symm (eOne.symm z, b)) then 1 else 0) := by
      calc
        (∑ a : (I → Ω), ∑ b : (O → Ω),
            Pone.w a * Pout.w b * (if Bad (ePi.symm (a, b)) then 1 else 0)) =
          ∑ a : (I → Ω), ∑ b : (O → Ω),
            (P i).w (eOne a) * Pout.w b * (if Bad (ePi.symm (a, b)) then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro b hb
              rw [hOneWeight]
        _ = ∑ z : Ω, ∑ b : (O → Ω),
            (P i).w z * Pout.w b *
              (if Bad (ePi.symm (eOne.symm z, b)) then 1 else 0) := by
              exact Fintype.sum_equiv eOne _ _ (by intro a; simp)
    _ = ∑ z : Ω, ∑ b : (O → Ω),
          (P i).w z * Pout.w b *
            (if Bad (Function.update (base b) i z) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro b hb
      rw [hbaseUpdate]
    _ = ∑ b : (O → Ω), (Pout.w b) *
          ∑ z : Ω, (P i).w z *
            (if Bad (Function.update (base b) i z) then 1 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ ≤ ∑ b : (O → Ω), Pout.w b * B := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hcond (base b)) (Pout.nonneg b)
    _ = B := by
      rw [← Finset.sum_mul, Pout.sum_eq_one]
      ring

private theorem keyDist_triangle
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)
    (g h k : Γ.Key) : Γ.keyDist g k ≤ Γ.keyDist g h + Γ.keyDist h k := by
  unfold GridGeom.keyDist
  calc
    (∑ r, Nat.dist (g r) (k r)) ≤
        ∑ r, (Nat.dist (g r) (h r) + Nat.dist (h r) (k r)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact Nat.dist.triangle_inequality (g r) (h r) (k r)
    _ = (∑ r, Nat.dist (g r) (h r)) + ∑ r, Nat.dist (h r) (k r) :=
      Finset.sum_add_distrib

private theorem auxDist_triangle
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)
    (t u w : Γ.AuxWord) : Γ.auxDist t w ≤ Γ.auxDist t u + Γ.auxDist u w := by
  classical
  let A := Finset.univ.filter (fun j => t j ≠ w j)
  let B := Finset.univ.filter (fun j => t j ≠ u j)
  let C := Finset.univ.filter (fun j => u j ≠ w j)
  have hsubset : A ⊆ B ∪ C := by
    intro j hj
    have hmem := (Finset.mem_filter.mp hj).1
    have hne := (Finset.mem_filter.mp hj).2
    by_cases htu : t j ≠ u j
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem, htu⟩)
    · have heq : t j = u j := by
        by_contra h
        exact htu h
      have huw : u j ≠ w j := by
        intro h
        exact hne (heq.trans h)
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmem, huw⟩)
  have hcard : A.card ≤ B.card + C.card :=
    (Finset.card_le_card hsubset).trans (Finset.card_union_le B C)
  simpa [A, B, C, GridGeom.auxDist] using hcard

theorem cellDist_triangle
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)
    (a b c : Γ.Cell) : Γ.cellDist a c ≤ Γ.cellDist a b + Γ.cellDist b c := by
  have hk := keyDist_triangle Γ a.1 b.1 c.1
  have ht := auxDist_triangle Γ a.2 b.2 c.2
  unfold GridGeom.cellDist at *
  omega

theorem fullNames_cellDist_le_one
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)
    (c w : Γ.Cell) (hw : w ∈ Γ.fullNames c) : Γ.cellDist c w ≤ 1 := by
  classical
  unfold GridGeom.fullNames at hw
  rcases List.mem_append.mp hw with hcross | hown
  · unfold GridGeom.crossNames at hcross
    rcases List.mem_map.mp hcross with ⟨h, hh, rfl⟩
    have hkey : h ∈ Γ.keyNbrs c.1 := by
      simpa [GridGeom.crossKeys] using hh
    have hdist : Γ.keyDist c.1 h = 1 := (Finset.mem_filter.mp hkey).2
    simp [GridGeom.cellDist, GridGeom.auxDist, hdist]
  · unfold GridGeom.ownNames at hown
    rcases List.mem_map.mp hown with ⟨t, ht, rfl⟩
    have hword : t ∈ Γ.auxBall c.2 1 := by
      simpa [GridGeom.ownWords] using ht
    have hdist : Γ.auxDist c.2 t ≤ 1 := (Finset.mem_filter.mp hword).2
    simpa [GridGeom.cellDist, GridGeom.keyDist] using hdist

private theorem cellLabels_eq_of_fullNames
    {d : ℝ} {n s ℓ q N : ℕ}
    (Γ : GridGeom d n s ℓ q) (W W' : Γ.Cell → Fin N) (c : Γ.Cell)
    (hW : ∀ w ∈ Γ.fullNames c, W w = W' w) :
    cellLabels Γ W c = cellLabels Γ W' c := by
  unfold cellLabels
  apply List.map_congr_left
  intro w hw
  exact hW w hw

private theorem crossLabels_eq_of_fullNames
    {d : ℝ} {n s ℓ q N : ℕ}
    (Γ : GridGeom d n s ℓ q) (W W' : Γ.Cell → Fin N) (c : Γ.Cell)
    (hW : ∀ w ∈ Γ.fullNames c, W w = W' w) :
    crossLabels Γ W c = crossLabels Γ W' c := by
  unfold crossLabels
  apply List.map_congr_left
  intro w hw
  exact hW w (List.mem_append.mpr (Or.inl hw))

private theorem crossValid_eq_of_fullNames
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (W W' : Γ.Cell → Fin N) (c : Γ.Cell)
    (hW : ∀ w ∈ Γ.fullNames c, W w = W' w) :
    CrossValidRow Γ M (σ c.1) (fun h => W (h, c.2)) c.1 ↔
      CrossValidRow Γ M (σ c.1) (fun h => W' (h, c.2)) c.1 := by
  classical
  have horder (h₀ : Γ.Key) (hh₀ : h₀ ∈ Γ.crossKeys c.1) :
      (Γ.crossOrder c.1 h₀).map (fun h => W (h, c.2)) =
        (Γ.crossOrder c.1 h₀).map (fun h => W' (h, c.2)) := by
    apply List.map_congr_left
    intro h hh
    have hmem : h ∈ Γ.crossKeys c.1 := by
      unfold GridGeom.crossOrder at hh
      rcases List.mem_append.mp hh with hmem | hmem
      · exact List.mem_of_mem_erase hmem
      · have : h = h₀ := List.mem_singleton.mp hmem
        simpa [this] using hh₀
    have hfull : (h, c.2) ∈ Γ.fullNames c := by
      unfold GridGeom.fullNames
      apply List.mem_append.mpr
      left
      unfold GridGeom.crossNames
      exact List.mem_map.mpr ⟨h, hmem, rfl⟩
    exact hW (h, c.2) hfull
  unfold CrossValidRow
  constructor
  · intro h h₀ hh₀ k hk
    have hh := h h₀ hh₀ k hk
    simpa [horder h₀ hh₀] using hh
  · intro h h₀ hh₀ k hk
    have hh := h h₀ hh₀ k hk
    simpa [horder h₀ hh₀] using hh

private theorem cellValid_eq_of_fullNames
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (W W' : Γ.Cell → Fin N) (c : Γ.Cell)
    (hW : ∀ w ∈ Γ.fullNames c, W w = W' w) :
    CellValid Γ M σ W c ↔ CellValid Γ M σ W' c := by
  have hcross := crossLabels_eq_of_fullNames Γ W W' c hW
  have hcell := cellLabels_eq_of_fullNames Γ W W' c hW
  have hOwn : OwnValid Γ M (σ c.1) W c = OwnValid Γ M (σ c.1) W' c := by
    unfold OwnValid
    rw [hcross, hcell]
  have hCross :
      CrossValidRow Γ M (σ c.1) (fun h => W (h, c.2)) c.1 =
        CrossValidRow Γ M (σ c.1) (fun h => W' (h, c.2)) c.1 :=
    propext (crossValid_eq_of_fullNames Γ M σ W W' c hW)
  simp [CellValid, hCross, hOwn]

theorem cellRow_eq_of_fullNames
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (W W' : Γ.Cell → Fin N) (c : Γ.Cell)
    (hW : ∀ w ∈ Γ.fullNames c, W w = W' w) (y : Fin N) :
    cellRow Γ M σ W c y = cellRow Γ M σ W' c y := by
  have hvalid := cellValid_eq_of_fullNames Γ M σ W W' c hW
  have hlabels := cellLabels_eq_of_fullNames Γ W W' c hW
  simp [cellRow, propext hvalid, hlabels]

private theorem delRow_eq_of_fullNames
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (W W' : Γ.Cell → Fin N) (c w : Γ.Cell)
    (hW : ∀ x ∈ Γ.fullNames c, W x = W' x) (hdel : W w = W' w) :
    delRow Γ M σ W c w = delRow Γ M σ W' c w := by
  unfold delRow
  rw [cellLabels_eq_of_fullNames Γ W W' c hW, hdel]

private theorem alarmRate_eq_of_anchorBall
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hloc : GeomLocal Γ) (σ : Γ.Key → M.ι)
    (W W' : Γ.Cell → Fin N) (c : Γ.Cell)
    (hW : ∀ x ∈ Γ.cellBall c 2, W x = W' x)
    (v : CubeVertex n) (hv : Γ.key v = c) :
    alarmRate Γ M σ W v = alarmRate Γ M σ W' v := by
  classical
  have hcenter (j : Fin n) : Γ.cellDist c (Γ.key (cubeFlip v j)) ≤ 1 := by
    simpa [hv] using hloc.flip_dist v j
  have hnames (j : Fin n) (x : Γ.Cell) (hx : x ∈ Γ.fullNames (Γ.key (cubeFlip v j))) :
      Γ.cellDist c x ≤ 2 := by
    have h := cellDist_triangle Γ c (Γ.key (cubeFlip v j)) x
    exact le_trans h (by
      have h1 := hcenter j
      have h2 := fullNames_cellDist_le_one Γ _ _ hx
      omega)
  have hWnames (j : Fin n) :
      ∀ x ∈ Γ.fullNames (Γ.key (cubeFlip v j)), W x = W' x := by
    intro x hx
    apply hW x
    simp [GridGeom.cellBall, hnames j x hx]
  have hWupdate (j : Fin n) (z : Fin N) :
      ∀ x ∈ Γ.fullNames (Γ.key (cubeFlip v j)),
        Function.update W c z x = Function.update W' c z x := by
    intro x hx
    by_cases hxc : x = c
    · simp [hxc]
    · simp [Function.update, hxc, hWnames j x hx]
  have hrow (j : Fin n) (y : Fin n → Fin N) :
      cellRow Γ M σ W (Γ.key (cubeFlip v j)) (y j) =
        cellRow Γ M σ W' (Γ.key (cubeFlip v j)) (y j) :=
    cellRow_eq_of_fullNames Γ M σ W W' (Γ.key (cubeFlip v j)) (hWnames j) (y j)
  have hlik (z : Fin N) (y : Fin n → Fin N) :
      starLik Γ M σ W v z y = starLik Γ M σ W' v z y := by
    simp only [starLik]
    rw [hv]
    apply Finset.prod_congr rfl
    intro j hj
    exact cellRow_eq_of_fullNames Γ M σ
      (Function.update W c z) (Function.update W' c z) (Γ.key (cubeFlip v j))
      (hWupdate j z) (y j)
  have hmarg (y : Fin n → Fin N) :
      starMarg Γ M σ W v y = starMarg Γ M σ W' v y := by
    unfold starMarg
    apply Finset.sum_congr rfl
    intro z hz
    rw [hlik z y]
  have hdeleted : W c = W' c := by
    apply hW c
    simp [GridGeom.cellBall, GridGeom.cellDist, GridGeom.keyDist, GridGeom.auxDist]
  have hdel (j : Fin n) :
      delRow Γ M σ W (Γ.key (cubeFlip v j)) c =
        delRow Γ M σ W' (Γ.key (cubeFlip v j)) c :=
    delRow_eq_of_fullNames Γ M σ W W' (Γ.key (cubeFlip v j)) c (hWnames j) hdeleted
  have href (y : Fin n → Fin N) :
      starRef Γ M σ W v y = starRef Γ M σ W' v y := by
    unfold starRef
    rw [hv]
    apply Finset.prod_congr rfl
    intro j hj
    rw [hdel j]
  have hpred (y : Fin n → Fin N) :
      PredFail Γ M σ W v y ↔ PredFail Γ M σ W' v y := by
    simp [PredFail, hmarg y, href y]
  unfold alarmRate
  apply Finset.sum_congr rfl
  intro y hy
  have hprod :
      (∏ j, cellRow Γ M σ W (Γ.key (cubeFlip v j)) (y j)) =
        ∏ j, cellRow Γ M σ W' (Γ.key (cubeFlip v j)) (y j) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact hrow j y
  rw [hprod, propext (hpred y)]

private theorem cellBad_eq_of_anchorBall
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hloc : GeomLocal Γ) (σ : Γ.Key → M.ι)
    (W W' : Γ.Cell → Fin N) (c : Γ.Cell)
    (hW : ∀ x ∈ Γ.cellBall c 2, W x = W' x) :
    CellBad Γ M σ W c ↔ CellBad Γ M σ W' c := by
  have hnames : ∀ x ∈ Γ.fullNames c, Γ.cellDist c x ≤ 2 := by
    intro x hx
    have h := fullNames_cellDist_le_one Γ c x hx
    omega
  have hfull : ∀ x ∈ Γ.fullNames c, W x = W' x := by
    intro x hx
    exact hW x (by simp [GridGeom.cellBall, hnames x hx])
  have hvalid := cellValid_eq_of_fullNames Γ M σ W W' c hfull
  have halarm : Alarm Γ M σ W c ↔ Alarm Γ M σ W' c := by
    constructor
    · rintro ⟨a, ha, hr⟩
      refine ⟨a, ha, ?_⟩
      have hrate := alarmRate_eq_of_anchorBall Γ M hloc σ W W' c hW a.1 ha
      rw [hrate] at hr
      exact hr
    · rintro ⟨a, ha, hr⟩
      refine ⟨a, ha, ?_⟩
      have hrate := alarmRate_eq_of_anchorBall Γ M hloc σ W W' c hW a.1 ha
      rw [hrate.symm] at hr
      exact hr
  simp [CellBad, hvalid, halarm]

theorem cellBad_depends_anchorBall_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hloc : GeomLocal Γ) (σ : Γ.Key → M.ι) (c : Γ.Cell) :
    FinProb.DependsOn (fun W => CellBad Γ M σ W c) (Γ.cellBall c 2) := by
  intro W W' hW
  exact propext (cellBad_eq_of_anchorBall Γ M hloc σ W W' c hW)

private theorem cellDist_comm
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)
    (a b : Γ.Cell) : Γ.cellDist a b = Γ.cellDist b a := by
  simp [GridGeom.cellDist, GridGeom.keyDist, GridGeom.auxDist,
    Nat.dist_comm, ne_comm]

theorem anchorLLL_of_local_bounds_q_s07_anchor
    {D₀ d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (hG : GeomFacts Γ)
    (hInvalid : CellInvalidBound Γ M σ) (hAlarm : AlarmProb Γ M σ)
    (hTag : ∀ g, ¬ TagBad Γ M D₀ σ g)
    (hx0 : 0 ≤ xL D₀ n) (hx1 : xL D₀ n < 1)
    (hnum : (n : ℝ) ^ (-(D₀ / 2)) +
        (n : ℝ) ^ 2 * ((q : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) +
        ((n : ℝ) + 1) ^ (2 * s + 1) * Real.exp (-(2 / 100 : ℝ) * q) ≤
      xL D₀ n * (1 - xL D₀ n) ^ ((2 * s + q + 1) ^ 4)) :
    AnchorLLL Γ M D₀ σ := by
  classical
  change LLLInput (fun c : Γ.Cell => M.μ (σ c.1))
    (fun c W => CellBad Γ M σ W c) (fun c => Γ.cellBall c 2)
    (xL D₀ n) ((2 * s + q + 1) ^ 4)
  let P : Γ.Cell → FinProb (Fin N) := fun c => M.μ (σ c.1)
  refine ⟨hx0, hx1, ?_, ?_, ?_⟩
  · intro c
    exact cellBad_depends_anchorBall_q_s07_anchor Γ M hG.loc σ c
  · intro c
    let badNbrs : Finset Γ.Cell := Finset.univ.filter fun c' =>
      c' ≠ c ∧ ¬ Disjoint (Γ.cellBall c 2) (Γ.cellBall c' 2)
    have hsubset : badNbrs ⊆ Γ.cellBall c 4 := by
      intro c' hc'
      have hc' := (Finset.mem_filter.mp hc').2
      rcases Finset.not_disjoint_iff.mp hc'.2 with ⟨w, hwc, hwc'⟩
      have hcw : Γ.cellDist c w ≤ 2 := (Finset.mem_filter.mp hwc).2
      have hc'w : Γ.cellDist c' w ≤ 2 := (Finset.mem_filter.mp hwc').2
      have hwc' : Γ.cellDist w c' ≤ 2 := by simpa [cellDist_comm Γ] using hc'w
      have hcc' := cellDist_triangle Γ c w c'
      have hdist : Γ.cellDist c c' ≤ 4 := by omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩
    have hcard : badNbrs.card ≤ (2 * s + q + 1) ^ 4 := by
      calc
        badNbrs.card ≤ (Γ.cellBall c 4).card := Finset.card_le_card hsubset
        _ ≤ (2 * s + q + 1) ^ 4 := by exact_mod_cast hG.balls.cellBall_card c 4
    simpa [LLLInput, badNbrs] using hcard
  · intro c
    have hcross : crossFailKey Γ M σ c.1 ≤ (n : ℝ) ^ (-(D₀ / 2)) := by
      exact le_of_not_gt (hTag c.1)
    have hAlarmGlobal :
        (FinProb.pi P).pr (fun W => Alarm Γ M σ W c) ≤
          ((n : ℝ) + 1) ^ (2 * s + 1) * Real.exp (-(2 / 100 : ℝ) * q) := by
      apply pi_pr_le_of_cond_coordinate P c (fun W => Alarm Γ M σ W c) _
      intro W
      simpa [P] using hAlarm W c
    have hUnion := FinProb.pr_union (FinProb.pi P)
      (fun W => ¬ CellValid Γ M σ W c) (fun W => Alarm Γ M σ W c)
    calc
      (FinProb.pi P).pr (fun W => CellBad Γ M σ W c) ≤
          (FinProb.pi P).pr (fun W => ¬ CellValid Γ M σ W c) +
            (FinProb.pi P).pr (fun W => Alarm Γ M σ W c) := by
        simpa [CellBad] using hUnion
      _ ≤ (n : ℝ) ^ (-(D₀ / 2)) +
            (n : ℝ) ^ 2 * ((q : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) +
            ((n : ℝ) + 1) ^ (2 * s + 1) * Real.exp (-(2 / 100 : ℝ) * q) := by
        have hinvalid := hInvalid c
        have hfirst := add_le_add hinvalid hAlarmGlobal
        calc
          _ ≤ (crossFailKey Γ M σ c.1 +
              (n : ℝ) ^ 2 * ((q : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p)) +
                ((n : ℝ) + 1) ^ (2 * s + 1) * Real.exp (-(2 / 100 : ℝ) * q) := hfirst
          _ ≤ _ := by nlinarith [hcross]
      _ ≤ xL D₀ n * (1 - xL D₀ n) ^ ((2 * s + q + 1) ^ 4) := hnum

theorem alarmRate_relabel_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N)
    (v v' : CubeVertex n) (hcenter : Γ.key v = Γ.key v')
    (e : Fin n ≃ Fin n)
    (hneighbor : ∀ j, Γ.key (cubeFlip v j) = Γ.key (cubeFlip v' (e j))) :
    alarmRate Γ M σ W v = alarmRate Γ M σ W v' := by
  classical
  let reindex : (Fin n → Fin N) ≃ (Fin n → Fin N) :=
    Equiv.piCongrLeft' (fun _ : Fin n => Fin N) e
  have hLikelihood (W' : Γ.Cell → Fin N) (y : Fin n → Fin N) :
      (∏ j, cellRow Γ M σ W' (Γ.key (cubeFlip v j)) (y j)) =
        ∏ j, cellRow Γ M σ W' (Γ.key (cubeFlip v' j)) (reindex y j) := by
    calc
      (∏ j, cellRow Γ M σ W' (Γ.key (cubeFlip v j)) (y j)) =
          ∏ j, cellRow Γ M σ W' (Γ.key (cubeFlip v' (e j))) (y j) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hneighbor j]
      _ = ∏ j, cellRow Γ M σ W' (Γ.key (cubeFlip v' j)) (reindex y j) := by
        exact Fintype.prod_equiv e _ _ (by intro j; simp [reindex])
  have hStar (z : Fin N) (y : Fin n → Fin N) :
      starLik Γ M σ W v z y = starLik Γ M σ W v' z (reindex y) := by
    simp only [starLik]
    rw [hcenter]
    exact hLikelihood (Function.update W (Γ.key v') z) y

  have hMarg (y : Fin n → Fin N) :
      starMarg Γ M σ W v y = starMarg Γ M σ W v' (reindex y) := by
    unfold starMarg
    rw [hcenter]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hStar z y]

  have hRef (y : Fin n → Fin N) :
      starRef Γ M σ W v y = starRef Γ M σ W v' (reindex y) := by
    unfold starRef
    rw [hcenter]
    exact Fintype.prod_equiv e _ _ (by intro j; simp [reindex, hneighbor j])

  have hPred (y : Fin n → Fin N) :
      PredFail Γ M σ W v y ↔ PredFail Γ M σ W v' (reindex y) := by
    simp [PredFail, hMarg y, hRef y]

  unfold alarmRate
  calc
    (∑ y, (∏ j, cellRow Γ M σ W (Γ.key (cubeFlip v j)) (y j)) *
          (if PredFail Γ M σ W v y then 1 else 0)) =
        ∑ y, (∏ j, cellRow Γ M σ W (Γ.key (cubeFlip v' j)) (reindex y j)) *
          (if PredFail Γ M σ W v' (reindex y) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hLikelihood W y, propext (hPred y)]
    _ = ∑ y, (∏ j, cellRow Γ M σ W (Γ.key (cubeFlip v' j)) (y j)) *
          (if PredFail Γ M σ W v' y then 1 else 0) := by
      exact Fintype.sum_equiv reindex _ _ (by intro y; rfl)

private theorem equiv_of_fiber_card_eq {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (f g : α → β)
    (h : ∀ b, (Finset.univ.filter fun a => f a = b).card =
      (Finset.univ.filter fun a => g a = b).card) :
    ∃ e : α ≃ α, ∀ a, g (e a) = f a := by
  classical
  have hcard (b : β) : Fintype.card {a // f a = b} = Fintype.card {a // g a = b} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h b
  let fiberEquiv : ∀ b, {a // f a = b} ≃ {a // g a = b} := fun b =>
    Fintype.equivOfCardEq (hcard b)
  refine ⟨Equiv.ofFiberEquiv fiberEquiv, ?_⟩
  intro a
  exact Equiv.ofFiberEquiv_map fiberEquiv a

private noncomputable def alarmVariableCells
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) (c : Γ.Cell) : Finset Γ.Cell :=
  insert c ((Γ.keyNbrs c.1).image fun h => (h, c.2))

private theorem keyGrid_flip_aux
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) (v : CubeVertex n)
    (j : Fin n) (hj : j ∈ Γ.aux) :
    (Γ.key (cubeFlip v j)).1 = (Γ.key v).1 := by
  classical
  funext r
  have hfilter :
    (Γ.chunk r).filter (fun k => cubeFlip v j k = true) =
        (Γ.chunk r).filter (fun k => v k = true) := by
    apply Finset.filter_congr
    intro k hk
    have hnot : j ∉ Γ.chunk r := by
      intro hmem
      exact (Finset.disjoint_left.mp (Γ.aux_disjoint r)) hj hmem
    have hkj : k ≠ j := by
      intro h
      subst k
      exact hnot hk
    simp [cubeFlip, hkj]
  change (Γ.bin r ⟨_, _⟩) = (Γ.bin r ⟨_, _⟩)
  congr 1
  apply Fin.ext
  exact congrArg Finset.card hfilter

private theorem keyAux_flip_nonaux
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) (v : CubeVertex n)
    (j : Fin n) (hj : j ∉ Γ.aux) :
    (Γ.key (cubeFlip v j)).2 = (Γ.key v).2 := by
  classical
  funext k
  have hkj : (k : Fin n) ≠ j := by
    intro h
    subst j
    exact hj k.property
  simp [GridGeom.key, cubeFlip, hkj]

private theorem key_flip_aux_eq
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)
    (v v' : CubeVertex n) (hcenter : Γ.key v = Γ.key v')
    (j : Fin n) (hj : j ∈ Γ.aux) :
    Γ.key (cubeFlip v j) = Γ.key (cubeFlip v' j) := by
  apply Prod.ext
  · calc
      (Γ.key (cubeFlip v j)).1 = (Γ.key v).1 := keyGrid_flip_aux Γ v j hj
      _ = (Γ.key v').1 := congrArg Prod.fst hcenter
      _ = (Γ.key (cubeFlip v' j)).1 := (keyGrid_flip_aux Γ v' j hj).symm
  · funext k
    have hbit : v k = v' k := by
      simpa [GridGeom.key] using congrArg (fun f => f k) (congrArg Prod.snd hcenter)
    by_cases hkj : (k : Fin n) = j
    · have hk : k = ⟨j, hj⟩ := Subtype.ext hkj
      subst k
      simp [GridGeom.key, cubeFlip, hbit]
    · simp [GridGeom.key, cubeFlip, hbit, hkj]

private theorem keyDist_eq_zero
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) {g h : Γ.Key}
    (hd : Γ.keyDist g h = 0) : g = h := by
  funext r
  have hterm : Nat.dist (g r : ℕ) (h r : ℕ) ≤ Γ.keyDist g h := by
    unfold GridGeom.keyDist
    exact Finset.single_le_sum (f := fun t => Nat.dist (g t : ℕ) (h t : ℕ))
      (fun t _ => Nat.zero_le _) (Finset.mem_univ r)
  have hzero : Nat.dist (g r : ℕ) (h r : ℕ) = 0 := by rw [hd] at hterm; omega
  apply Fin.ext
  exact Nat.eq_of_dist_eq_zero hzero

private theorem key_flip_nonaux_mem
    {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) (hloc : GeomLocal Γ)
    (v : CubeVertex n) (j : Fin n) (hj : j ∉ Γ.aux) :
    Γ.key (cubeFlip v j) ∈ alarmVariableCells Γ (Γ.key v) := by
  classical
  let c := Γ.key v
  let c' := Γ.key (cubeFlip v j)
  have haux : c'.2 = c.2 := by
    exact keyAux_flip_nonaux Γ v j hj
  have hdist : Γ.keyDist c.1 c'.1 ≤ 1 := by
    have hcell := hloc.flip_dist v j
    have hword : Γ.auxDist c.2 c'.2 = 0 := by simp [GridGeom.auxDist, haux]
    unfold GridGeom.cellDist at hcell
    rw [hword] at hcell
    omega
  by_cases hsame : c.1 = c'.1
  · have hcell : c' = c := by
      rcases c with ⟨g, t⟩
      rcases c' with ⟨g', t'⟩
      simp_all
    change c' ∈ insert c ((Γ.keyNbrs c.1).image fun h => (h, c.2))
    rw [hcell]
    exact Finset.mem_insert_self _ _
  · have hdist1 : Γ.keyDist c.1 c'.1 = 1 := by
      have hne : Γ.keyDist c.1 c'.1 ≠ 0 := by
        intro hz
        have heq := keyDist_eq_zero Γ hz
        exact hsame heq
      omega
    have hmem : c'.1 ∈ Γ.keyNbrs c.1 := by
      simp [GridGeom.keyNbrs, hdist1]
    have hcell : c' = (c'.1, c.2) := by
      rcases c' with ⟨g', t'⟩
      simpa using haux
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨c'.1, hmem, hcell.symm⟩

theorem alarm_reps_q_s07_anchor
    {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (hloc : GeomLocal Γ) (M : Menu7 n N E G X Y d p κ) :
    AlarmReps Γ M := by
  classical
  intro c
  let V : Finset Γ.Cell := alarmVariableCells Γ c
  let VX := {x : Γ.Cell // x ∈ V}
  let Aux := {j : Fin n // j ∈ Γ.aux}
  let Bucket := VX ⊕ Aux
  let Roles := {a : EvenRole n // Γ.key a.1 = c}
  let Profiles := VX → Fin (n + 1)
  have hVcard : V.card ≤ 2 * s + 1 := by
    dsimp [V, alarmVariableCells]
    calc
      (insert c ((Γ.keyNbrs c.1).image fun h => (h, c.2))).card ≤
          ((Γ.keyNbrs c.1).image fun h => (h, c.2)).card + 1 := Finset.card_insert_le _ _
      _ ≤ (Γ.keyNbrs c.1).card + 1 := Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ 2 * s + 1 := Nat.add_le_add_right (hloc.keyNbrs_card c.1) 1
  by_cases hRoles : Nonempty Roles
  · let bucket : Roles → Fin n → Bucket := fun a j =>
      if hj : j ∈ Γ.aux then Sum.inr ⟨j, hj⟩ else
        Sum.inl ⟨Γ.key (cubeFlip a.1.1 j), by
          simpa [V, a.2] using key_flip_nonaux_mem Γ hloc a.1.1 j hj⟩
    let profile : Roles → Profiles := fun a x =>
      ⟨(Finset.univ.filter fun j : Fin n => bucket a j = Sum.inl x).card, by
        have hle := Finset.card_filter_le (Finset.univ : Finset (Fin n))
          (fun j => bucket a j = Sum.inl x)
        simpa using Nat.lt_succ_of_le hle⟩
    let pset : Finset Profiles := Finset.univ.image profile
    let pick : Profiles → Roles := fun p =>
      if h : ∃ a : Roles, profile a = p then Classical.choose h else Classical.choice hRoles
    let reps : Finset Roles := pset.image pick
    let S : Finset (EvenRole n) := reps.image Subtype.val
    have hSkey : ∀ a ∈ S, Γ.key a.1 = c := by
      intro a ha
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
      subst a
      exact b.2
    have hScard : S.card ≤ (n + 1) ^ (2 * s + 1) := by
      calc
        S.card ≤ reps.card := Finset.card_image_le
        _ ≤ pset.card := Finset.card_image_le
        _ ≤ Fintype.card Profiles := Finset.card_le_univ _
        _ = (n + 1) ^ V.card := by simp [Profiles, VX]
        _ ≤ (n + 1) ^ (2 * s + 1) :=
          Nat.pow_le_pow_right (by omega) hVcard
    refine ⟨S, hScard, hSkey, ?_⟩
    intro a ha
    let aa : Roles := ⟨a, ha⟩
    let p₀ : Profiles := profile aa
    have hp₀ : p₀ ∈ pset := Finset.mem_image.mpr ⟨aa, Finset.mem_univ _, rfl⟩
    have hchoose : ∃ b : Roles, profile b = p₀ := ⟨aa, rfl⟩
    have hpick : profile (pick p₀) = p₀ := by
      dsimp [pick]
      rw [dif_pos hchoose]
      exact Classical.choose_spec hchoose
    let bb : Roles := pick p₀
    have hprof : profile aa = profile bb := by
      exact hpick.symm
    have hcenter : Γ.key a.1 = Γ.key bb.1.1 := by
      calc
        Γ.key a.1 = c := ha
        _ = Γ.key bb.1.1 := bb.2.symm
    have hcount (x : Bucket) :
        (Finset.univ.filter fun j : Fin n => bucket aa j = x).card =
          (Finset.univ.filter fun j : Fin n => bucket bb j = x).card := by
      cases x with
      | inl x =>
          simpa [profile, bucket] using congrArg Fin.val (congrFun hprof x)
      | inr j =>
          have hfilter (a : Roles) :
              Finset.univ.filter (fun k : Fin n => bucket a k = Sum.inr j) = {j.1} := by
            ext k
            by_cases hkj : k = j.1
            · subst k
              simp [bucket, j.property]
            · have hneq : bucket a k ≠ Sum.inr (α := VX) j := by
                by_cases hk : k ∈ Γ.aux
                · intro heq
                  have hbucket : bucket a k =
                      Sum.inr (α := VX) (⟨k, hk⟩ : Aux) := by simp [bucket, hk]
                  rw [hbucket] at heq
                  have hsub : (⟨k, hk⟩ : Aux) = j := Sum.inr.inj heq
                  exact hkj (congrArg Subtype.val hsub)
                · simp [bucket, hk]
              simp [hneq, hkj]
          rw [hfilter aa, hfilter bb]
    have hcount' : ∀ x : Bucket,
        (Finset.univ.filter fun j : Fin n => bucket aa j = x).card =
          (Finset.univ.filter fun j : Fin n => bucket bb j = x).card := by
      intro x
      exact hcount x
    obtain ⟨e, he⟩ := equiv_of_fiber_card_eq (α := Fin n) (β := Bucket)
      (bucket aa) (bucket bb) hcount'
    have hneighbor : ∀ j,
        Γ.key (cubeFlip a.1 j) = Γ.key (cubeFlip bb.1.1 (e j)) := by
      intro j
      have hbucket := he j
      by_cases hj : j ∈ Γ.aux
      · have hej : e j ∈ Γ.aux := by
          by_contra hnot
          have hbad := hbucket
          simp [bucket, hj, hnot] at hbad
        have hindex : e j = j := by
          have hsum : Sum.inr (α := VX) (⟨e j, hej⟩ : Aux) =
              Sum.inr (α := VX) ⟨j, hj⟩ := by
            simpa only [bucket, dif_pos hj, dif_pos hej] using hbucket
          exact congrArg Subtype.val (Sum.inr.inj hsum)
        rw [hindex]
        exact key_flip_aux_eq Γ a.1 bb.1.1 hcenter j hj
      · have hmemA : Γ.key (cubeFlip a.1 j) ∈ V := by
          have h := key_flip_nonaux_mem Γ hloc a.1 j hj
          rw [aa.2] at h
          simpa [V] using h
        have hbucket' : Sum.inl ⟨Γ.key (cubeFlip a.1 j), hmemA⟩ = bucket bb (e j) := by
          simpa [bucket, hj] using hbucket.symm
        have hnot : e j ∉ Γ.aux := by
          by_contra hbad
          simp [bucket, hbad] at hbucket'
        have hmemB : Γ.key (cubeFlip bb.1.1 (e j)) ∈ V := by
          have h := key_flip_nonaux_mem Γ hloc bb.1.1 (e j) hnot
          rw [bb.2] at h
          simpa [V] using h
        have hbucket'' : bucket bb (e j) =
            Sum.inl ⟨Γ.key (cubeFlip bb.1.1 (e j)), hmemB⟩ := by
          simp [bucket, hnot]
        have hsum : Sum.inl (⟨Γ.key (cubeFlip a.1 j), hmemA⟩ : VX) =
            Sum.inl ⟨Γ.key (cubeFlip bb.1.1 (e j)), hmemB⟩ := hbucket'.trans hbucket''
        exact congrArg Subtype.val (Sum.inl.inj hsum)
    have hS : bb.1 ∈ S := by
      apply Finset.mem_image.mpr
      refine ⟨bb, ?_, rfl⟩
      apply Finset.mem_image.mpr
      exact ⟨p₀, hp₀, rfl⟩
    refine ⟨bb.1, hS, ?_⟩
    intro σ W
    exact alarmRate_relabel_q_s07_anchor Γ M σ W a.1 bb.1.1 hcenter e hneighbor
  · refine ⟨∅, by simp, ?_, ?_⟩
    · intro a ha
      simp at ha
    · intro a ha
      exact (hRoles ⟨a, ha⟩).elim

private theorem anchor_geom_ceil_bounds (d : ℝ) (hd : 0 < d) {n : ℕ}
    (hn : 2 ≤ n) :
    (gS d n : ℝ) ≤ 2 * (n : ℝ) ^ d ∧
    (n : ℝ) ^ (4 * d) ≤ (gQ d n : ℝ) ∧
    (gQ d n : ℝ) ≤ 2 * (n : ℝ) ^ (4 * d) := by
  have hnreal : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hd4 : 0 < 4 * d := by positivity
  have hpow : 1 < (n : ℝ) ^ d := Real.one_lt_rpow hnreal hd
  have hpow4 : 1 < (n : ℝ) ^ (4 * d) := Real.one_lt_rpow hnreal hd4
  have hsceil : (gS d n : ℝ) < (n : ℝ) ^ d + 1 := by
    dsimp [gS]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) d)
  have hqceil : (gQ d n : ℝ) < (n : ℝ) ^ (4 * d) + 1 := by
    dsimp [gQ]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) (4 * d))
  have hqLower : (n : ℝ) ^ (4 * d) ≤ (gQ d n : ℝ) := by
    dsimp [gQ]
    exact_mod_cast Nat.le_ceil ((n : ℝ) ^ (4 * d))
  refine ⟨?_, hqLower, ?_⟩
  · nlinarith
  · nlinarith

theorem one_sub_pow_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    1 - (m : ℝ) * x ≤ (1 - x) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hbase0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
      have hbase1 : 1 - x ≤ 1 := sub_le_self 1 hx0
      have hpow : (1 - x) ^ m ≤ 1 := pow_le_one₀ hbase0 hbase1
      calc
        1 - ((m + 1 : ℕ) : ℝ) * x = (1 - (m : ℝ) * x) - x := by push_cast; ring
        _ ≤ (1 - x) ^ m - x := sub_le_sub_right ih x
        _ ≤ (1 - x) ^ m * (1 - x) := by nlinarith [mul_le_mul_of_nonneg_left hpow hx0]
        _ = (1 - x) ^ (m + 1) := by rw [pow_succ]

private theorem anchor_lll_cross_ratio_tendsto (D₀ : ℝ) (hD₀ : 0 < D₀) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-(D₀ / 2)) / xL D₀ n) atTop (𝓝 0) := by
  have heq : (fun n : ℕ => (n : ℝ) ^ (-(D₀ / 2)) / xL D₀ n) =ᶠ[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(D₀ / 4)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [xL]
    rw [← Real.rpow_sub hnpos]
    congr 1
    ring
  exact (tendsto_congr' heq).mpr
    ((tendsto_rpow_neg_atTop (by positivity : 0 < D₀ / 4)).comp
      tendsto_natCast_atTop_atTop)

private theorem anchor_lll_own_ratio_tendsto
    (D₀ d p : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d) (hp : 0 < p) :
    Tendsto (fun n : ℕ =>
      (n : ℝ) ^ 2 * ((gQ d n : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) /
        xL D₀ n) atTop (𝓝 0) := by
  classical
  let A : ℝ := 2 + 4 * d + D₀ / 4
  let ratio : ℕ → ℝ := fun n =>
    (n : ℝ) ^ 2 * ((gQ d n : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) /
      xL D₀ n
  let major : ℕ → ℝ := fun n => (n : ℝ) ^ A * Real.exp (-(n : ℝ) ^ p)
  have hnp : Tendsto (fun n : ℕ => (n : ℝ) ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  have hmajorBase :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / p) 1 one_pos).comp hnp
  have heq : major =ᶠ[atTop] fun n : ℕ =>
      ((n : ℝ) ^ p) ^ (A / p) * Real.exp (-1 * (n : ℝ) ^ p) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hA : A = p * (A / p) := by dsimp [A]; field_simp [hp.ne']
    have hA0 : (n : ℝ) ^ A = (n : ℝ) ^ (p * (A / p)) :=
      congrArg (fun z => (n : ℝ) ^ z) hA
    have hPowA : (n : ℝ) ^ A = ((n : ℝ) ^ p) ^ (A / p) := by
      exact hA0.trans (Real.rpow_mul (le_of_lt hnpos) p (A / p))
    dsimp [major]
    calc
      (n : ℝ) ^ A * Real.exp (-(n : ℝ) ^ p) =
          ((n : ℝ) ^ p) ^ (A / p) * Real.exp (-(n : ℝ) ^ p) :=
        congrArg (fun t => t * Real.exp (-(n : ℝ) ^ p)) hPowA
      _ = ((n : ℝ) ^ p) ^ (A / p) * Real.exp (-1 * (n : ℝ) ^ p) := by
        simp
  have hmajor : Tendsto major atTop (𝓝 0) := (tendsto_congr' heq).mpr hmajorBase
  have h3major : Tendsto (fun n => 3 * major n) atTop (𝓝 0) := by
    simpa [major] using (tendsto_const_nhds (x := (3 : ℝ))).mul hmajor
  have hratioNonneg : ∀ n, 0 ≤ ratio n := by
    intro n
    dsimp [ratio]
    apply div_nonneg
    · positivity
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hratioLe : ∀ᶠ n : ℕ in atTop, ratio n ≤ 3 * major n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    obtain ⟨hs, hqlo, hqhi⟩ := anchor_geom_ceil_bounds d hd hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hqpow : 1 ≤ (n : ℝ) ^ (4 * d) := le_of_lt
      (Real.one_lt_rpow (by exact_mod_cast (show 1 < n by omega)) (by positivity))
    have hqplus : (gQ d n : ℝ) + 1 ≤ 3 * (n : ℝ) ^ (4 * d) := by nlinarith
    have hxinv : (xL D₀ n)⁻¹ = (n : ℝ) ^ (D₀ / 4) := by
      dsimp [xL]
      rw [Real.rpow_neg (le_of_lt hnpos)]
      simp
    have hpow : (n : ℝ) ^ 2 * (n : ℝ) ^ (4 * d) * (n : ℝ) ^ (D₀ / 4) =
        (n : ℝ) ^ A := by
      rw [← Real.rpow_natCast (n : ℝ) 2,
        ← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
      rfl
    dsimp [ratio]
    rw [div_eq_mul_inv, hxinv]
    calc
      (n : ℝ) ^ 2 * ((gQ d n : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) *
          (n : ℝ) ^ (D₀ / 4) ≤
        (n : ℝ) ^ 2 * (3 * (n : ℝ) ^ (4 * d)) *
          Real.exp (-(n : ℝ) ^ p) * (n : ℝ) ^ (D₀ / 4) := by
            gcongr
      _ = 3 * ((n : ℝ) ^ 2 * (n : ℝ) ^ (4 * d) *
          (n : ℝ) ^ (D₀ / 4)) * Real.exp (-(n : ℝ) ^ p) := by ring
      _ = 3 * major n := by
        rw [hpow]
        ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3major
    (Eventually.of_forall hratioNonneg) hratioLe

theorem anchor_lll_numeric_q_s07_anchor
    (D₀ d p : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d)
    (hd' : d < D₀ / 1000) (hp : 0 < p) :
    ∃ n₀, ∀ n ≥ n₀,
      0 ≤ xL D₀ n ∧ xL D₀ n < 1 ∧
        xL D₀ n * ((2 * gS d n + gQ d n + 1 : ℕ) : ℝ) ^ 4 ≤ 1 / 2 ∧
        (n : ℝ) ^ (-(D₀ / 2)) +
          (n : ℝ) ^ 2 * ((gQ d n : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) +
          ((n : ℝ) + 1) ^ (2 * gS d n + 1) *
            Real.exp (-(2 / 100 : ℝ) * gQ d n) ≤
          xL D₀ n * (1 - xL D₀ n) ^ ((2 * gS d n + gQ d n + 1) ^ 4) := by
  classical
  let x : ℕ → ℝ := fun n => xL D₀ n
  let crossRatio : ℕ → ℝ := fun n => (n : ℝ) ^ (-(D₀ / 2)) / x n
  let ownRatio : ℕ → ℝ := fun n =>
    (n : ℝ) ^ 2 * ((gQ d n : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) / x n
  let alarmRatio : ℕ → ℝ := fun n =>
    ((n : ℝ) + 1) ^ (2 * gS d n + 1) *
      Real.exp (-(2 / 100 : ℝ) * gQ d n) / x n
  let degreeRatio : ℕ → ℝ := fun n =>
    x n * ((2 * gS d n + gQ d n + 1 : ℕ) : ℝ) ^ 4
  let Aexp : ℝ := 2 + 4 * d + D₀ / 4
  have hxT : Tendsto x atTop (𝓝 0) := by
    dsimp [x, xL]
    exact (tendsto_rpow_neg_atTop (by positivity : 0 < D₀ / 4)).comp
      tendsto_natCast_atTop_atTop
  have hcrossT : Tendsto crossRatio atTop (𝓝 0) := by
    have heq : crossRatio =ᶠ[atTop] fun n : ℕ => (n : ℝ) ^ (-(D₀ / 4)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      dsimp [crossRatio, x, xL]
      rw [← Real.rpow_sub hnpos]
      congr 1
      ring
    exact (tendsto_congr' heq).mpr
      ((tendsto_rpow_neg_atTop (by positivity : 0 < D₀ / 4)).comp
        tendsto_natCast_atTop_atTop)
  have hNP : Tendsto (fun n : ℕ => (n : ℝ) ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  have hOwnBase : Tendsto
      (fun n : ℕ => ((n : ℝ) ^ p) ^ (Aexp / p) * Real.exp (-1 * (n : ℝ) ^ p))
      atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (Aexp / p) 1 one_pos).comp hNP
  have hOwnEq :
      (fun n : ℕ => (n : ℝ) ^ Aexp * Real.exp (-(n : ℝ) ^ p)) =ᶠ[atTop]
        fun n : ℕ => ((n : ℝ) ^ p) ^ (Aexp / p) * Real.exp (-1 * (n : ℝ) ^ p) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hA : Aexp = p * (Aexp / p) := by
      dsimp [Aexp]
      field_simp [hp.ne']
    have hA0 : (n : ℝ) ^ Aexp = (n : ℝ) ^ (p * (Aexp / p)) :=
      congrArg (fun z => (n : ℝ) ^ z) hA
    have hPowA : (n : ℝ) ^ Aexp = ((n : ℝ) ^ p) ^ (Aexp / p) := by
      exact hA0.trans (Real.rpow_mul (le_of_lt hnpos) p (Aexp / p))
    calc
      (n : ℝ) ^ Aexp * Real.exp (-(n : ℝ) ^ p) =
          ((n : ℝ) ^ p) ^ (Aexp / p) * Real.exp (-(n : ℝ) ^ p) :=
        congrArg (fun t => t * Real.exp (-(n : ℝ) ^ p)) hPowA
      _ = ((n : ℝ) ^ p) ^ (Aexp / p) * Real.exp (-1 * (n : ℝ) ^ p) := by
        simp
  have hOwnBase' : Tendsto
      (fun n : ℕ => (n : ℝ) ^ Aexp * Real.exp (-(n : ℝ) ^ p)) atTop (𝓝 0) :=
    (tendsto_congr' hOwnEq).mpr hOwnBase
  have h3OwnBase : Tendsto
      (fun n : ℕ => 3 * ((n : ℝ) ^ Aexp * Real.exp (-(n : ℝ) ^ p))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (3 : ℝ))).mul hOwnBase'
  have hownNonneg : ∀ n, 0 ≤ ownRatio n := by
    intro n
    apply div_nonneg
    · positivity
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hownUpper : ∀ᶠ n : ℕ in atTop,
      ownRatio n ≤ 3 * ((n : ℝ) ^ Aexp * Real.exp (-(n : ℝ) ^ p)) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    obtain ⟨hs, hqlo, hqhi⟩ := anchor_geom_ceil_bounds d hd hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hqbase : 1 ≤ (n : ℝ) ^ (4 * d) := le_of_lt (Real.one_lt_rpow
      (by exact_mod_cast (show 1 < n by omega)) (by positivity))
    have hqplus : (gQ d n : ℝ) + 1 ≤ 3 * (n : ℝ) ^ (4 * d) := by nlinarith
    have hxinv : (x n)⁻¹ = (n : ℝ) ^ (D₀ / 4) := by
      dsimp [x, xL]
      rw [Real.rpow_neg (le_of_lt hnpos)]
      simp
    have hpow : (n : ℝ) ^ 2 * (n : ℝ) ^ (4 * d) * (n : ℝ) ^ (D₀ / 4) =
        (n : ℝ) ^ Aexp := by
      rw [← Real.rpow_natCast (n : ℝ) 2,
        ← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
      rfl
    dsimp [ownRatio]
    rw [div_eq_mul_inv, hxinv]
    calc
      (n : ℝ) ^ 2 * ((gQ d n : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) *
          (n : ℝ) ^ (D₀ / 4) ≤
        (n : ℝ) ^ 2 * (3 * (n : ℝ) ^ (4 * d)) *
          Real.exp (-(n : ℝ) ^ p) * (n : ℝ) ^ (D₀ / 4) := by
            gcongr
      _ = 3 * ((n : ℝ) ^ Aexp * Real.exp (-(n : ℝ) ^ p)) := by
        calc
          (n : ℝ) ^ 2 * (3 * (n : ℝ) ^ (4 * d)) *
              Real.exp (-(n : ℝ) ^ p) * (n : ℝ) ^ (D₀ / 4) =
              3 * ((n : ℝ) ^ 2 * (n : ℝ) ^ (4 * d) *
                (n : ℝ) ^ (D₀ / 4)) * Real.exp (-(n : ℝ) ^ p) := by ring
          _ = 3 * ((n : ℝ) ^ Aexp * Real.exp (-(n : ℝ) ^ p)) := by
            rw [hpow]
            ring
  have hOwnT : Tendsto ownRatio atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3OwnBase
      (Eventually.of_forall hownNonneg) hownUpper
  have hCrossSmall : ∀ᶠ n : ℕ in atTop, crossRatio n < 1 / 8 := by
    exact hcrossT.eventually (Iio_mem_nhds (by norm_num))
  have hOwnSmall : ∀ᶠ n : ℕ in atTop, ownRatio n < 1 / 8 := by
    exact hOwnT.eventually (Iio_mem_nhds (by norm_num))
  let alarmExp : ℕ → ℝ := fun n =>
    ((2 * gS d n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) -
      (2 / 100 : ℝ) * gQ d n + (D₀ / 4) * Real.log (n : ℝ)
  have hpowLog (n : ℕ) :
      ((n : ℝ) + 1) ^ (2 * gS d n + 1) =
        Real.exp (((2 * gS d n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1)) := by
    rw [← Real.rpow_natCast]
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  have hxExp (n : ℕ) (hn : 2 ≤ n) :
      x n = Real.exp (-(D₀ / 4) * Real.log (n : ℝ)) := by
    dsimp [x, xL]
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  have hAlarmEq (n : ℕ) (hn : 2 ≤ n) :
      alarmRatio n = Real.exp (alarmExp n) := by
    have hpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    dsimp [alarmRatio]
    rw [hpowLog n, hxExp n hn, div_eq_mul_inv]
    calc
      Real.exp (((2 * gS d n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1)) *
          Real.exp (-(2 / 100 : ℝ) * gQ d n) *
            (Real.exp (-(D₀ / 4) * Real.log (n : ℝ)))⁻¹ =
          Real.exp (((2 * gS d n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) -
            (2 / 100 : ℝ) * gQ d n + (D₀ / 4) * Real.log (n : ℝ)) := by
        rw [← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ = Real.exp (alarmExp n) := by rfl
  have hExpNeg2 : Real.exp (-2 : ℝ) < 1 / 4 := by
    have h2 : (4 : ℝ) < Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_gt_two, Real.exp_pos (1 : ℝ)]
    rw [Real.exp_neg]
    simpa [one_div] using (one_div_lt_one_div_of_lt (by norm_num) h2)
  let eps : ℝ := d / 2
  let C : ℝ := 5 * (2 : ℝ) ^ eps / eps + D₀ / (2 * d)
  have heps : 0 < eps := by positivity
  have hC : 0 ≤ C := by positivity
  have hN4 : Tendsto (fun n : ℕ => (n : ℝ) ^ (4 * d)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 4 * d)).comp tendsto_natCast_atTop_atTop
  have hN4large : ∀ᶠ n : ℕ in atTop, (200 : ℝ) ≤ (n : ℝ) ^ (4 * d) :=
    hN4.eventually (eventually_ge_atTop (200 : ℝ))
  have hCratio : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-(2 * d))) atTop (𝓝 0) := by
    have hpow := (tendsto_rpow_neg_atTop (by positivity : 0 < 2 * d)).comp
      tendsto_natCast_atTop_atTop
    simpa [mul_comm] using (tendsto_const_nhds (x := C)).mul hpow
  have hCsmall : ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ (-(2 * d)) < 1 / 100 :=
    hCratio.eventually (Iio_mem_nhds (by norm_num))
  have halarmLogBound (n : ℕ) (hn : 2 ≤ n) :
      alarmExp n ≤ C * (n : ℝ) ^ (2 * d) - (2 / 100 : ℝ) * (n : ℝ) ^ (4 * d) := by
    obtain ⟨hs, hqlo, hqhi⟩ := anchor_geom_ceil_bounds d hd hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnreal : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    have hpowd : 1 ≤ (n : ℝ) ^ d := le_of_lt (Real.one_lt_rpow hnreal hd)
    have hhalf_le : eps ≤ 2 * d := by dsimp [eps]; linarith
    have hthreehalves_le : d + eps ≤ 2 * d := by dsimp [eps]; linarith
    have hpowHalf : (n : ℝ) ^ eps ≤ (n : ℝ) ^ (2 * d) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hnreal) hhalf_le
    have hpowThreeHalves : (n : ℝ) ^ (d + eps) ≤ (n : ℝ) ^ (2 * d) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hnreal) hthreehalves_le
    have hcoeff : ((2 * gS d n + 1 : ℕ) : ℝ) ≤ 5 * (n : ℝ) ^ d := by
      push_cast
      nlinarith [hs, hpowd]
    have hlog1 : Real.log ((n : ℝ) + 1) ≤
        ((2 : ℝ) ^ eps / eps) * (n : ℝ) ^ eps := by
      have hlog := Real.log_natCast_le_rpow_div (n + 1) heps
      have hbase : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by nlinarith
      have hpow := Real.rpow_le_rpow (by positivity) hbase (le_of_lt heps)
      have hpow' : ((n : ℝ) + 1) ^ eps ≤ (2 : ℝ) ^ eps * (n : ℝ) ^ eps := by
        calc
          ((n : ℝ) + 1) ^ eps ≤ (2 * (n : ℝ)) ^ eps := hpow
          _ = (2 : ℝ) ^ eps * (n : ℝ) ^ eps := by
            rw [Real.mul_rpow (by norm_num) (by positivity)]
      have hpowCast : (((n + 1 : ℕ) : ℝ) ^ eps) ≤
          (2 : ℝ) ^ eps * (n : ℝ) ^ eps := by
        simpa [Nat.cast_add, Nat.cast_one] using hpow'
      calc
        Real.log ((n : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) ^ eps / eps := by
          simpa [Nat.cast_add, Nat.cast_one] using hlog
        _ ≤ ((2 : ℝ) ^ eps * (n : ℝ) ^ eps) / eps :=
          div_le_div_of_nonneg_right hpowCast (by positivity)
        _ = ((2 : ℝ) ^ eps / eps) * (n : ℝ) ^ eps := by ring
    have hlogN : Real.log (n : ℝ) ≤ (n : ℝ) ^ eps / eps := by
      exact Real.log_natCast_le_rpow_div n heps
    have hterm1 : ((2 * gS d n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) ≤
        (5 * (2 : ℝ) ^ eps / eps) * (n : ℝ) ^ (2 * d) := by
      calc
        _ ≤ (5 * (n : ℝ) ^ d) * (((2 : ℝ) ^ eps / eps) * (n : ℝ) ^ eps) :=
          mul_le_mul hcoeff hlog1 (Real.log_nonneg (by nlinarith)) (by positivity)
        _ = (5 * (2 : ℝ) ^ eps / eps) * (n : ℝ) ^ (d + eps) := by
          calc
            5 * (n : ℝ) ^ d * (((2 : ℝ) ^ eps / eps) * (n : ℝ) ^ eps) =
                (5 * (2 : ℝ) ^ eps / eps) *
                  ((n : ℝ) ^ d * (n : ℝ) ^ eps) := by ring
            _ = (5 * (2 : ℝ) ^ eps / eps) * (n : ℝ) ^ (d + eps) := by
              rw [← Real.rpow_add hnpos]
        _ ≤ (5 * (2 : ℝ) ^ eps / eps) * (n : ℝ) ^ (2 * d) :=
          mul_le_mul_of_nonneg_left hpowThreeHalves (by positivity)
    have hterm2 : (D₀ / 4) * Real.log (n : ℝ) ≤
        (D₀ / (2 * d)) * (n : ℝ) ^ (2 * d) := by
      calc
        (D₀ / 4) * Real.log (n : ℝ) ≤
            (D₀ / 4) * ((n : ℝ) ^ eps / eps) :=
          mul_le_mul_of_nonneg_left hlogN (by positivity)
        _ = (D₀ / (2 * d)) * (n : ℝ) ^ eps := by
          dsimp [eps]
          field_simp [ne_of_gt hd]
          ring
        _ ≤ (D₀ / (2 * d)) * (n : ℝ) ^ (2 * d) :=
          mul_le_mul_of_nonneg_left hpowHalf (by positivity)
    dsimp [alarmExp, C]
    nlinarith [hterm1, hterm2, hqlo]
  have hAlarmSmall : ∀ᶠ n : ℕ in atTop, alarmRatio n < 1 / 4 := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hCsmall, hN4large]
      with n hn hCs hN4n
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hpowcombine : (n : ℝ) ^ (-(2 * d)) * (n : ℝ) ^ (4 * d) =
        (n : ℝ) ^ (2 * d) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    have hCterm : C * (n : ℝ) ^ (2 * d) ≤ (1 / 100 : ℝ) * (n : ℝ) ^ (4 * d) := by
      calc
        C * (n : ℝ) ^ (2 * d) =
            (C * (n : ℝ) ^ (-(2 * d))) * (n : ℝ) ^ (4 * d) := by
          rw [← hpowcombine]
          ring
        _ ≤ (1 / 100 : ℝ) * (n : ℝ) ^ (4 * d) :=
          mul_le_mul_of_nonneg_right (le_of_lt hCs) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hL : alarmExp n ≤ -2 := by
      calc
        alarmExp n ≤ C * (n : ℝ) ^ (2 * d) - (2 / 100 : ℝ) * (n : ℝ) ^ (4 * d) :=
          halarmLogBound n hn
        _ ≤ (1 / 100 : ℝ) * (n : ℝ) ^ (4 * d) -
            (2 / 100 : ℝ) * (n : ℝ) ^ (4 * d) := by linarith [hCterm]
        _ = -(1 / 100 : ℝ) * (n : ℝ) ^ (4 * d) := by ring
        _ ≤ -2 := by nlinarith [hN4n]
    have hEq := hAlarmEq n hn
    rw [hEq]
    exact (Real.exp_le_exp.mpr hL).trans_lt hExpNeg2
  let gap : ℝ := D₀ / 4 - 16 * d
  have hgap : 0 < gap := by
    dsimp [gap]
    nlinarith [hd']
  have hdegreeNonneg : ∀ n, 0 ≤ degreeRatio n := by
    intro n
    dsimp [degreeRatio]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (pow_nonneg (Nat.cast_nonneg _) 4)
  have hdegreeUpper : ∀ᶠ n : ℕ in atTop,
      degreeRatio n ≤ (7 : ℝ) ^ 4 * (n : ℝ) ^ (-gap) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    obtain ⟨hs, hqlo, hqhi⟩ := anchor_geom_ceil_bounds d hd hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnreal : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    have hpowMon : (n : ℝ) ^ d ≤ (n : ℝ) ^ (4 * d) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hnreal) (by linarith)
    have hone : 1 ≤ (n : ℝ) ^ (4 * d) :=
      le_of_lt (Real.one_lt_rpow hnreal (by positivity))
    have hbase : ((2 * gS d n + gQ d n + 1 : ℕ) : ℝ) ≤
        7 * (n : ℝ) ^ (4 * d) := by
      push_cast
      nlinarith [hs, hqhi, hpowMon, hone]
    have hpowBase : (((2 * gS d n + gQ d n + 1 : ℕ) : ℝ) ^ 4) ≤
        (7 * (n : ℝ) ^ (4 * d)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hbase 4
    have hpow4 : ((n : ℝ) ^ (4 * d)) ^ 4 = (n : ℝ) ^ (16 * d) := by
      calc
        ((n : ℝ) ^ (4 * d)) ^ 4 = ((n : ℝ) ^ (4 * d)) ^ (4 : ℝ) :=
          (Real.rpow_natCast ((n : ℝ) ^ (4 * d)) 4).symm
        _ = (n : ℝ) ^ ((4 * d) * 4) :=
          (Real.rpow_mul (le_of_lt hnpos) (4 * d) (4 : ℝ)).symm
        _ = (n : ℝ) ^ (16 * d) := by congr 1 <;> ring
    dsimp [degreeRatio, x, xL]
    calc
      (n : ℝ) ^ (-(D₀ / 4)) *
          ((2 * gS d n + gQ d n + 1 : ℕ) : ℝ) ^ 4 ≤
        (n : ℝ) ^ (-(D₀ / 4)) * (7 * (n : ℝ) ^ (4 * d)) ^ 4 :=
          mul_le_mul_of_nonneg_left hpowBase (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = (7 : ℝ) ^ 4 * (n : ℝ) ^ (-gap) := by
        calc
          (n : ℝ) ^ (-(D₀ / 4)) * (7 * (n : ℝ) ^ (4 * d)) ^ 4 =
              (7 : ℝ) ^ 4 *
                ((n : ℝ) ^ (-(D₀ / 4)) * (n : ℝ) ^ (16 * d)) := by
                  rw [mul_pow, hpow4]
                  ring
          _ = (7 : ℝ) ^ 4 * (n : ℝ) ^ (-gap) := by
            rw [← Real.rpow_add hnpos]
            congr 1
            dsimp [gap]
            ring
  have hdegreeMajor : Tendsto
      (fun n : ℕ => (7 : ℝ) ^ 4 * (n : ℝ) ^ (-gap)) atTop (𝓝 0) := by
    have hpow := (tendsto_rpow_neg_atTop hgap).comp tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := (7 : ℝ) ^ 4)).mul hpow
  have hdegreeT : Tendsto degreeRatio atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdegreeMajor
      (Eventually.of_forall hdegreeNonneg) hdegreeUpper
  have hDegreeSmall : ∀ᶠ n : ℕ in atTop, degreeRatio n < 1 / 2 :=
    hdegreeT.eventually (Iio_mem_nhds (by norm_num))
  have hAllSmall : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ crossRatio n < 1 / 8 ∧ ownRatio n < 1 / 8 ∧
        alarmRatio n < 1 / 4 ∧ degreeRatio n < 1 / 2 := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hCrossSmall, hOwnSmall,
      hAlarmSmall, hDegreeSmall] with n hn hc ho ha hdg
    exact ⟨hn, hc, ho, ha, hdg⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hAllSmall
  refine ⟨n₀, ?_⟩
  intro n hn
  obtain ⟨hn2, hc, ho, ha, hdg⟩ := hn₀ n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnreal : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hxpos : 0 < x n := by
    dsimp [x, xL]
    exact Real.rpow_pos_of_pos hnpos _
  have hbase : 1 < (n : ℝ) ^ (D₀ / 4) :=
    Real.one_lt_rpow hnreal (by positivity)
  have hxform : x n = ((n : ℝ) ^ (D₀ / 4))⁻¹ := by
    dsimp [x, xL]
    rw [Real.rpow_neg (le_of_lt hnpos)]
  have hxlt : x n < 1 := by
    rw [hxform]
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hbase
    simpa using h
  have hratios :
      (n : ℝ) ^ (-(D₀ / 2)) +
        (n : ℝ) ^ 2 * ((gQ d n : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) +
        ((n : ℝ) + 1) ^ (2 * gS d n + 1) *
          Real.exp (-(2 / 100 : ℝ) * gQ d n) =
        x n * (crossRatio n + ownRatio n + alarmRatio n) := by
    dsimp [crossRatio, ownRatio, alarmRatio]
    field_simp [ne_of_gt hxpos]
  have hsum : crossRatio n + ownRatio n + alarmRatio n ≤ 1 / 2 := by
    linarith
  let m : ℕ := (2 * gS d n + gQ d n + 1) ^ 4
  have hm : (m : ℝ) * x n = degreeRatio n := by
    dsimp [m, degreeRatio]
    simp only [Nat.cast_pow]
    ring
  have hpowLower : (1 / 2 : ℝ) ≤ (1 - x n) ^ m := by
    have h := one_sub_pow_lower hxpos.le (le_of_lt hxlt) m
    rw [hm] at h
    linarith [hdg]
  have hRhs : x n / 2 ≤ x n * (1 - x n) ^ m := by
    calc
      x n / 2 = x n * (1 / 2) := by ring
      _ ≤ x n * (1 - x n) ^ m :=
        mul_le_mul_of_nonneg_left hpowLower hxpos.le
  have hLhs :
      (n : ℝ) ^ (-(D₀ / 2)) +
        (n : ℝ) ^ 2 * ((gQ d n : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) +
        ((n : ℝ) + 1) ^ (2 * gS d n + 1) *
          Real.exp (-(2 / 100 : ℝ) * gQ d n) ≤ x n / 2 := by
    rw [hratios]
    calc
      x n * (crossRatio n + ownRatio n + alarmRatio n) ≤ x n * (1 / 2) :=
        mul_le_mul_of_nonneg_left hsum hxpos.le
      _ = x n / 2 := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [x] using hxpos.le
  · simpa [x] using hxlt
  · dsimp [degreeRatio, x] at hdg ⊢
    exact le_of_lt hdg
  · calc
      (n : ℝ) ^ (-(D₀ / 2)) +
          (n : ℝ) ^ 2 * ((gQ d n : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) +
          ((n : ℝ) + 1) ^ (2 * gS d n + 1) *
            Real.exp (-(2 / 100 : ℝ) * gQ d n) ≤ x n / 2 := hLhs
      _ ≤ x n * (1 - x n) ^ m := hRhs
      _ = xL D₀ n * (1 - xL D₀ n) ^ ((2 * gS d n + gQ d n + 1) ^ 4) := by
        dsimp [x, m]
end HypercubeRamsey.S07
