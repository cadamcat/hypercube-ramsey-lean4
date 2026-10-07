import HypercubeRamsey.S08.L81.LoadNodes

noncomputable section

namespace HypercubeRamsey.S08

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators

theorem finProb_nonempty {α : Type*} [Fintype α] (P : FinProb α) : Nonempty α := by
  classical
  by_contra hne
  haveI : IsEmpty α := ⟨fun a => hne ⟨a⟩⟩
  have hsum : (∑ a, P.w a) = 0 := by simp
  rw [P.sum_eq_one] at hsum
  norm_num at hsum

theorem pi_pr_depends_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (S : Finset ι) (F : (∀ i, Ω i) → Prop) (ω₀ : ∀ i, Ω i)
    (hF : FinProb.DependsOn F S) :
    (FinProb.pi P).pr F =
      (FinProb.pi (fun i : {i // i ∈ S} => P i.1)).pr
        (fun a => F ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω).symm
          (a, fun i => ω₀ i.1))) := by
  classical
  let indicator : (∀ i, Ω i) → ℝ := fun ω => if F ω then 1 else 0
  have hind : FinProb.DependsOn indicator S := by
    intro ω ω' hω
    simp only [indicator]
    rw [hF ω ω' hω]
  have h := FinProb.pi_expect_depends P S indicator ω₀ hind
  simpa [indicator, FinProb.pr, FinProb.expect] using h

private theorem pi_weight_split_q_s08 {ι : Type*} [Fintype ι] [DecidableEq ι]
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

theorem pi_expect_split_full {ι : Type*} [Fintype ι] [DecidableEq ι]
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
  rw [pi_weight_split_q_s08 P s (e.symm (a, b))]
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

namespace Ctx

variable {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)

def crossCells (c : D.CellT) : Finset D.CellT :=
  Finset.univ.image fun u : D.CrossSub c.1 => (u.1, c.2)

theorem averageCoordinateMarginal_nonneg (Q : FinProb D.Tup) (y : Fin D.N) :
    0 ≤ averageCoordinateMarginal Q y := by
  unfold averageCoordinateMarginal
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro i hi
  exact pr_nonneg _ _

theorem lightMass_nonneg (Q : FinProb D.Tup) : 0 ≤ D.lightMass Q := by
  unfold lightMass
  apply Finset.sum_nonneg
  intro y hy
  apply mul_nonneg (D.averageCoordinateMarginal_nonneg Q y)
  split_ifs <;> norm_num

theorem p0w_sum_le_one (Θ : D.Hist) (P : D.Pos) (c : D.CellT) (π : D.Pres c.1) :
    ∑ y, D.p0w Θ P c π y ≤ 1 := by
  classical
  let Q := D.selPost Θ P c π
  change ∑ y, D.p0w Θ P c π y ≤ 1
  by_cases hL : D.lightMass Q = 0
  · simp [Ctx.p0w, Q, hL]
  · have hsum : (∑ y, D.p0w Θ P c π y) = 1 := by
      unfold Ctx.p0w
      have hLne : D.lightMass (D.selPost Θ P c π) ≠ 0 := by simpa [Q] using hL
      simp only [if_neg hLne]
      rw [← Finset.sum_div]
      change D.lightMass Q / D.lightMass Q = 1
      exact div_self (by simpa [Q] using hL)
    rw [hsum]

theorem p0_nonneg (q : D.Pre) (W : D.Anch) (c : D.CellT) (y : Fin D.N) :
    0 ≤ D.p0 q W c y := by
  unfold Ctx.p0
  split_ifs with hv
  · unfold Ctx.p0w
    by_cases hL : D.lightMass (D.selPost q.1.1 q.1.2 c (D.presOf q W c)) = 0
    · simp [hL]
    · have hmass := D.lightMass_nonneg (D.selPost q.1.1 q.1.2 c (D.presOf q W c))
      have hmasspos : 0 < D.lightMass (D.selPost q.1.1 q.1.2 c (D.presOf q W c)) :=
        lt_of_le_of_ne hmass (Ne.symm hL)
      simp only [if_neg hL]
      have hmask : (0 : ℝ) ≤ if y ∈ heavyCoordinateSet
          (D.selPost q.1.1 q.1.2 c (D.presOf q W c)) D.heavyB then 0 else 1 := by
        split_ifs <;> norm_num
      exact div_nonneg
        (mul_nonneg (D.averageCoordinateMarginal_nonneg
          (D.selPost q.1.1 q.1.2 c (D.presOf q W c)) y) hmask) hmasspos.le
  · exact le_rfl

theorem p0_sum_le_one (q : D.Pre) (W : D.Anch) (c : D.CellT) :
    ∑ y, D.p0 q W c y ≤ 1 := by
  unfold Ctx.p0
  split_ifs with hv
  · exact D.p0w_sum_le_one q.1.1 q.1.2 c (D.presOf q W c)
  · simp

theorem refRow_nonneg (q : D.Pre) (W : D.Anch) (e c : D.CellT) (y : Fin D.N) :
    0 ≤ D.refRow q W e c y := by
  unfold Ctx.refRow
  split_ifs with h
  · exact D.p0_nonneg q W c y
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem refRow_sum_le_one (q : D.Pre) (W : D.Anch) (e c : D.CellT) :
    ∑ y, D.refRow q W e c y ≤ 1 := by
  classical
  by_cases h : c.1 = e.1 ∧ D.PresValid q W c
  · simp [Ctx.refRow, h]
    exact D.p0_sum_le_one q W c
  · unfold Ctx.refRow
    simp only [h, ↓reduceIte]
    by_cases hN : D.N = 0
    · simp [hN]
    · have hNc : (D.N : ℝ) ≠ 0 := by exact_mod_cast hN
      simp [hNc]

theorem starRef_nonneg (q : D.Pre) (W : D.Anch) (v : CubeVertex D.n)
    (y : Fin D.n → Fin D.N) : 0 ≤ D.starRef q W v y := by
  unfold Ctx.starRef
  apply Finset.prod_nonneg
  intro j hj
  exact D.refRow_nonneg q W (cellOf η₀ v) (cellOf η₀ (cubeFlip v j)) (y j)

theorem starRef_sum_le_one (q : D.Pre) (W : D.Anch) (v : CubeVertex D.n) :
    ∑ y : Fin D.n → Fin D.N, D.starRef q W v y ≤ 1 := by
  classical
  unfold Ctx.starRef
  rw [← Fintype.prod_sum]
  calc
    ∏ j : Fin D.n, ∑ z : Fin D.N,
        D.refRow q W (cellOf η₀ v) (cellOf η₀ (cubeFlip v j)) z ≤
      ∏ j : Fin D.n, (1 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro j hj
          apply Finset.sum_nonneg
          intro z hz
          exact D.refRow_nonneg q W (cellOf η₀ v) (cellOf η₀ (cubeFlip v j)) z
        · intro j hj
          exact D.refRow_sum_le_one q W (cellOf η₀ v) (cellOf η₀ (cubeFlip v j))
    _ = 1 := by simp

theorem starMarg_update_eq (q : D.Pre) (W : D.Anch) (v : CubeVertex D.n) (z : Fin D.N)
    (y : Fin D.n → Fin D.N) :
    D.starMarg q (Function.update W (cellOf η₀ v) z) v y = D.starMarg q W v y := by
  unfold Ctx.starMarg Ctx.starLik
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp

theorem keyDist_self (g : D.KeyT) : keyDist g g = 0 := by
  simp [keyDist]

theorem crossKey_ne_self (c : D.CellT) (u : D.CrossSub c.1) : u.1 ≠ c.1 := by
  intro he
  have hu : keyDist c.1 u.1 = 1 := (Finset.mem_filter.mp u.2).2
  have : keyDist c.1 c.1 = 1 := by simpa [he] using hu
  rw [D.keyDist_self] at this
  omega

theorem presOf_update_eq (q : D.Pre) (W : D.Anch) (t : D.CellT) (z : Fin D.N) (c : D.CellT)
    (ht : ∀ u : D.CrossSub c.1, (u.1, c.2) ≠ t) :
    D.presOf q (Function.update W t z) c = D.presOf q W c := by
  apply Prod.ext
  · rfl
  · funext u
    have hu := ht u
    simp only [presOf]
    rw [Function.update_of_ne hu]

theorem presValid_update_eq (q : D.Pre) (W : D.Anch) (t : D.CellT) (z : Fin D.N) (c : D.CellT)
    (ht : ∀ u : D.CrossSub c.1, (u.1, c.2) ≠ t) :
    D.PresValid q (Function.update W t z) c = D.PresValid q W c := by
  have hp := D.presOf_update_eq q W t z c ht
  unfold PresValid
  rw [hp]

theorem p0_update_eq (q : D.Pre) (W : D.Anch) (t : D.CellT) (z : Fin D.N) (c : D.CellT)
    (ht : ∀ u : D.CrossSub c.1, (u.1, c.2) ≠ t) (y : Fin D.N) :
    D.p0 q (Function.update W t z) c y = D.p0 q W c y := by
  have hp := D.presOf_update_eq q W t z c ht
  have hv := D.presValid_update_eq q W t z c ht
  unfold p0
  rw [hv, hp]

theorem presOf_eq_of_crossCells (q : D.Pre) (W W' : D.Anch) (c : D.CellT)
    (hc : ∀ t ∈ D.crossCells c, W t = W' t) :
    D.presOf q W c = D.presOf q W' c := by
  apply Prod.ext
  · rfl
  · funext u
    have hu : (u.1, c.2) ∈ D.crossCells c :=
      Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    have hloc := hc (u.1, c.2) hu
    simp only [presOf]
    rw [hloc]

theorem denFail_eq_of_crossCells (q : D.Pre) (W W' : D.Anch) (c : D.CellT)
    (hc : ∀ t ∈ D.crossCells c, W t = W' t) :
    D.DenFail q W c = D.DenFail q W' c := by
  have hp := D.presOf_eq_of_crossCells q W W' c hc
  simp [Ctx.DenFail, hp]

theorem keyDist_triangle (g u w : D.KeyT) :
    keyDist g w ≤ keyDist g u + keyDist u w := by
  unfold keyDist
  calc
    (∑ r, Nat.dist (g r).val (w r).val) ≤
        ∑ r, (Nat.dist (g r).val (u r).val + Nat.dist (u r).val (w r).val) := by
          apply Finset.sum_le_sum
          intro r hr
          exact Nat.dist.triangle_inequality _ _ _
    _ = (∑ r, Nat.dist (g r).val (u r).val) +
        ∑ r, Nat.dist (u r).val (w r).val := Finset.sum_add_distrib

theorem cellDist_triangle (c e t : D.CellT) :
    cellDist c t ≤ cellDist c e + cellDist e t := by
  unfold cellDist
  have hk := D.keyDist_triangle c.1 e.1 t.1
  have hh : _root_.hammingDist c.2 t.2 ≤
      _root_.hammingDist c.2 e.2 + _root_.hammingDist e.2 t.2 :=
    _root_.hammingDist_triangle c.2 e.2 t.2
  omega

theorem padNbr_cellDist_le_one (c e : D.CellT) (hce : PadNbr c e) : cellDist c e ≤ 1 := by
  rcases hce with ⟨heq, hb⟩ | ⟨heq, hb⟩
  · have hh : hammingDist c.2 e.2 ≤ 1 := (Finset.mem_filter.mp hb).2
    change _root_.hammingDist c.2 e.2 ≤ 1 at hh
    unfold cellDist
    rw [heq, D.keyDist_self]
    simpa using hh
  · have hk : keyDist c.1 e.1 = 1 := (Finset.mem_filter.mp hb).2
    unfold cellDist
    rw [heq, hk]
    simp

theorem cellBall_chain (c e t : D.CellT) (hce : cellDist c e ≤ 1) (het : cellDist e t ≤ 1) :
    t ∈ cellBall c 2 := by
  apply Finset.mem_filter.mpr
  constructor
  · simp
  · calc
      cellDist c t ≤ cellDist c e + cellDist e t := D.cellDist_triangle c e t
      _ ≤ 1 + 1 := Nat.add_le_add hce het
      _ = 2 := by norm_num

theorem crossAnchor_mem_ball1 (c : D.CellT) (u : D.CrossSub c.1) :
    (u.1, c.2) ∈ cellBall c 1 := by
  apply Finset.mem_filter.mpr
  constructor
  · simp
  · have hu : keyDist c.1 u.1 = 1 := (Finset.mem_filter.mp u.2).2
    change keyDist c.1 u.1 + _root_.hammingDist c.2 c.2 ≤ 1
    rw [hu]
    rw [_root_.hammingDist_self]

theorem ordAnchor_mem_ball1 (c : D.CellT) {b : D.ResT} (hb : b ∈ ordNbrs c.2) :
    (c.1, b) ∈ cellBall c 1 := by
  apply Finset.mem_filter.mpr
  constructor
  · simp
  · have hh : hammingDist c.2 b ≤ 1 := (Finset.mem_filter.mp hb).2
    change _root_.hammingDist c.2 b ≤ 1 at hh
    change keyDist c.1 c.1 + _root_.hammingDist c.2 b ≤ 1
    rw [D.keyDist_self]
    simpa using hh

theorem presOf_eq_of_ball1 (q : D.Pre) (W W' : D.Anch) (c : D.CellT)
    (hc : ∀ t ∈ cellBall c 1, W t = W' t) :
    D.presOf q W c = D.presOf q W' c := by
  apply Prod.ext
  · rfl
  · funext u
    have hu := hc (u.1, c.2) (D.crossAnchor_mem_ball1 c u)
    simp only [presOf]
    rw [hu]

theorem presValid_eq_of_ball1 (q : D.Pre) (W W' : D.Anch) (c : D.CellT)
    (hc : ∀ t ∈ cellBall c 1, W t = W' t) :
    D.PresValid q W c = D.PresValid q W' c := by
  have hp := D.presOf_eq_of_ball1 q W W' c hc
  unfold PresValid
  rw [hp]

theorem p0_eq_of_ball1 (q : D.Pre) (W W' : D.Anch) (c : D.CellT) (y : Fin D.N)
    (hc : ∀ t ∈ cellBall c 1, W t = W' t) :
    D.p0 q W c y = D.p0 q W' c y := by
  have hp := D.presOf_eq_of_ball1 q W W' c hc
  have hv := D.presValid_eq_of_ball1 q W W' c hc
  unfold p0
  rw [hv, hp]

theorem ordHit_eq_of_ball1 (W W' : D.Anch) (c : D.CellT) (y : Fin D.N)
    (hc : ∀ t ∈ cellBall c 1, W t = W' t) :
    D.OrdHit W c y = D.OrdHit W' c y := by
  unfold Ctx.OrdHit
  apply propext
  constructor
  · intro hh b hb
    have hloc := hc (c.1, b) (D.ordAnchor_mem_ball1 c hb)
    rw [← hloc]
    exact hh b hb
  · intro hh b hb
    have hloc := hc (c.1, b) (D.ordAnchor_mem_ball1 c hb)
    rw [hloc]
    exact hh b hb

theorem ordRet_eq_of_ball1 (q : D.Pre) (W W' : D.Anch) (c : D.CellT)
    (hc : ∀ t ∈ cellBall c 1, W t = W' t) :
    D.ordRet q W c = D.ordRet q W' c := by
  unfold Ctx.ordRet
  apply Finset.sum_congr rfl
  intro y hy
  rw [D.p0_eq_of_ball1 q W W' c y hc, D.ordHit_eq_of_ball1 W W' c y hc]

theorem valid8_eq_of_ball1 (q : D.Pre) (W W' : D.Anch) (c : D.CellT)
    (hc : ∀ t ∈ cellBall c 1, W t = W' t) :
    D.Valid8 q W c = D.Valid8 q W' c := by
  unfold Ctx.Valid8
  rw [D.presValid_eq_of_ball1 q W W' c hc, D.ordRet_eq_of_ball1 q W W' c hc]

theorem prow_eq_of_ball1 (q : D.Pre) (W W' : D.Anch) (c : D.CellT) (y : Fin D.N)
    (hc : ∀ t ∈ cellBall c 1, W t = W' t) :
    D.prow q W c y = D.prow q W' c y := by
  have hp0 := D.p0_eq_of_ball1 q W W' c y hc
  have hhit := D.ordHit_eq_of_ball1 W W' c y hc
  have hv := D.valid8_eq_of_ball1 q W W' c hc
  have hret := D.ordRet_eq_of_ball1 q W W' c hc
  unfold Ctx.prow
  simp [hv, hp0, hhit, hret]

theorem cellBall_one_subset_two (c t : D.CellT) (ht : t ∈ cellBall c 1) : t ∈ cellBall c 2 := by
  apply Finset.mem_filter.mpr
  constructor
  · simp
  · have hdist := (Finset.mem_filter.mp ht).2
    omega

theorem prow_eq_of_ball2_neighbor (q : D.Pre) (W W' : D.Anch) (c e : D.CellT)
    (y : Fin D.N) (hce : cellDist c e ≤ 1)
    (hc : ∀ t ∈ cellBall c 2, W t = W' t) :
    D.prow q W e y = D.prow q W' e y := by
  apply D.prow_eq_of_ball1 q W W' e y
  intro t ht
  exact hc t (D.cellBall_chain c e t hce (Finset.mem_filter.mp ht).2)

theorem refRow_eq_of_ball1 (q : D.Pre) (W W' : D.Anch) (e c : D.CellT) (y : Fin D.N)
    (hc : ∀ t ∈ cellBall c 1, W t = W' t) :
    D.refRow q W e c y = D.refRow q W' e c y := by
  by_cases hk : c.1 = e.1
  · have hv := D.presValid_eq_of_ball1 q W W' c hc
    have hp := D.p0_eq_of_ball1 q W W' c y hc
    simp [Ctx.refRow, hk, hv, hp]
  · simp [Ctx.refRow, hk]

theorem refRow_eq_of_ball2_neighbor (q : D.Pre) (W W' : D.Anch) (c f : D.CellT)
    (y : Fin D.N) (hcf : cellDist c f ≤ 1)
    (hc : ∀ t ∈ cellBall c 2, W t = W' t) :
    D.refRow q W c f y = D.refRow q W' c f y := by
  apply D.refRow_eq_of_ball1 q W W' c f y
  intro t ht
  exact hc t (D.cellBall_chain c f t hcf (Finset.mem_filter.mp ht).2)

theorem cubeFlip_cellDist_le_one (hG : GridFacts η₀ D.n) (v : CubeVertex D.n) (j : Fin D.n) :
    cellDist (cellOf η₀ v) (cellOf η₀ (cubeFlip v j)) ≤ 1 := by
  exact D.padNbr_cellDist_le_one _ _ (hG.edge v (cubeFlip v j) (cubeFlip_adj v j))

theorem starRef_eq_of_ball2 (hG : GridFacts η₀ D.n) (q : D.Pre) (W W' : D.Anch)
    (v : CubeVertex D.n) (y : Fin D.n → Fin D.N)
    (hc : ∀ t ∈ cellBall (cellOf η₀ v) 2, W t = W' t) :
    D.starRef q W v y = D.starRef q W' v y := by
  unfold Ctx.starRef
  apply Finset.prod_congr rfl
  intro j hj
  exact D.refRow_eq_of_ball2_neighbor q W W' (cellOf η₀ v)
    (cellOf η₀ (cubeFlip v j)) (y j) (D.cubeFlip_cellDist_le_one hG v j) hc

theorem starLik_eq_of_ball2 (hG : GridFacts η₀ D.n) (q : D.Pre) (W W' : D.Anch)
    (v : CubeVertex D.n) (z : Fin D.N) (y : Fin D.n → Fin D.N)
    (hc : ∀ t ∈ cellBall (cellOf η₀ v) 2, W t = W' t) :
    D.starLik q W v z y = D.starLik q W' v z y := by
  unfold Ctx.starLik
  apply Finset.prod_congr rfl
  intro j hj
  let e : D.CellT := cellOf η₀ v
  let f : D.CellT := cellOf η₀ (cubeFlip v j)
  have hef : cellDist e f ≤ 1 := D.cubeFlip_cellDist_le_one hG v j
  have hlocal : ∀ t ∈ cellBall f 1,
      Function.update W e z t = Function.update W' e z t := by
    intro t ht
    by_cases hte : t = e
    · subst t
      simp
    · have hbase := hc t (D.cellBall_chain e f t hef (Finset.mem_filter.mp ht).2)
      simp [Function.update, hte, hbase]
  exact D.prow_eq_of_ball1 q (Function.update W e z) (Function.update W' e z) f (y j) hlocal

theorem starMarg_eq_of_ball2 (hG : GridFacts η₀ D.n) (q : D.Pre) (W W' : D.Anch)
    (v : CubeVertex D.n) (y : Fin D.n → Fin D.N)
    (hc : ∀ t ∈ cellBall (cellOf η₀ v) 2, W t = W' t) :
    D.starMarg q W v y = D.starMarg q W' v y := by
  unfold Ctx.starMarg
  apply Finset.sum_congr rfl
  intro z hz
  rw [D.starLik_eq_of_ball2 hG q W W' v z y hc]

theorem predFail_eq_of_ball2 (hG : GridFacts η₀ D.n) (q : D.Pre) (W W' : D.Anch)
    (v : CubeVertex D.n) (y : Fin D.n → Fin D.N)
    (hc : ∀ t ∈ cellBall (cellOf η₀ v) 2, W t = W' t) :
    D.PredFail q W v y = D.PredFail q W' v y := by
  unfold Ctx.PredFail
  rw [D.starMarg_eq_of_ball2 hG q W W' v y hc,
    D.starRef_eq_of_ball2 hG q W W' v y hc]

theorem alarmRate_eq_of_ball2 (hG : GridFacts η₀ D.n) (q : D.Pre) (W W' : D.Anch)
    (v : CubeVertex D.n)
    (hc : ∀ t ∈ cellBall (cellOf η₀ v) 2, W t = W' t) :
    D.alarmRate q W v = D.alarmRate q W' v := by
  unfold Ctx.alarmRate
  apply Finset.sum_congr rfl
  intro y hy
  have hprod :
      (∏ j, D.prow q W (cellOf η₀ (cubeFlip v j)) (y j)) =
        ∏ j, D.prow q W' (cellOf η₀ (cubeFlip v j)) (y j) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact D.prow_eq_of_ball2_neighbor q W W' (cellOf η₀ v)
      (cellOf η₀ (cubeFlip v j)) (y j) (D.cubeFlip_cellDist_le_one hG v j) hc
  rw [hprod, D.predFail_eq_of_ball2 hG q W W' v y hc]

theorem alarm_eq_of_ball2 (hG : GridFacts η₀ D.n) (q : D.Pre) (W W' : D.Anch) (c : D.CellT)
    (hc : ∀ t ∈ cellBall c 2, W t = W' t) :
    D.Alarm q W c = D.Alarm q W' c := by
  unfold Ctx.Alarm
  apply propext
  constructor
  · rintro ⟨a, ha, hrate⟩
    refine ⟨a, ha, ?_⟩
    have hcell : cellOf η₀ a.1 = c := ha
    have hrate' := D.alarmRate_eq_of_ball2 hG q W W' a.1 (by
      intro t ht
      exact hc t (by simpa [hcell] using ht))
    rw [hrate'] at hrate
    exact hrate
  · rintro ⟨a, ha, hrate⟩
    refine ⟨a, ha, ?_⟩
    have hcell : cellOf η₀ a.1 = c := ha
    have hrate' := D.alarmRate_eq_of_ball2 hG q W W' a.1 (by
      intro t ht
      exact hc t (by simpa [hcell] using ht))
    rw [hrate']
    exact hrate

theorem denFail_eq_of_ball1 (q : D.Pre) (W W' : D.Anch) (c : D.CellT)
    (hc : ∀ t ∈ cellBall c 1, W t = W' t) :
    D.DenFail q W c = D.DenFail q W' c := by
  have hp := D.presOf_eq_of_ball1 q W W' c hc
  simp [Ctx.DenFail, hp]

theorem hitFail_eq_of_ball1 (q : D.Pre) (W W' : D.Anch) (c : D.CellT)
    (hc : ∀ t ∈ cellBall c 1, W t = W' t) :
    D.HitFail q W c = D.HitFail q W' c := by
  have hr := D.ordRet_eq_of_ball1 q W W' c hc
  simp [Ctx.HitFail, hr]

theorem cellBad_eq_of_ball2 (hG : GridFacts η₀ D.n) (q : D.Pre) (W W' : D.Anch) (c : D.CellT)
    (hc : ∀ t ∈ cellBall c 2, W t = W' t) :
    D.CellBad q W c = D.CellBad q W' c := by
  have hc1 : ∀ t ∈ cellBall c 1, W t = W' t := by
    intro t ht
    exact hc t (D.cellBall_one_subset_two c t ht)
  unfold Ctx.CellBad
  rw [D.denFail_eq_of_ball1 q W W' c hc1,
    D.hitFail_eq_of_ball1 q W W' c hc1,
    D.alarm_eq_of_ball2 hG q W W' c hc]

theorem keyOf_cubeFlip_eq_of_ge (v : CubeVertex D.n) (j : Fin D.n)
    (hjm : mC η₀ D.n ≤ j.val) :
    keyOf η₀ (cubeFlip v j) = keyOf η₀ v := by
  funext r
  apply Fin.ext
  simp only [keyOf, Fin.val_mk]
  congr 1
  unfold chunkWeight
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hi, hrest, hbit⟩
    refine ⟨hi, hrest, ?_⟩
    have hne : i ≠ j := by
      intro heq
      subst i
      omega
    simpa [cubeFlip, hne] using hbit
  · rintro ⟨hi, hrest, hbit⟩
    refine ⟨hi, hrest, ?_⟩
    have hne : i ≠ j := by
      intro heq
      subst i
      omega
    simpa [cubeFlip, hne] using hbit

theorem keyFlip_card_le_m (v : CubeVertex D.n) :
    ((Finset.univ.filter fun j : Fin D.n => keyOf η₀ (cubeFlip v j) ≠ keyOf η₀ v).card : ℕ) ≤
      mC η₀ D.n := by
  classical
  let s : Finset (Fin D.n) := Finset.univ.filter
    fun j => keyOf η₀ (cubeFlip v j) ≠ keyOf η₀ v
  let t : Finset (Fin D.n) := Finset.univ.filter fun j => j.val < mC η₀ D.n
  have hst : s ⊆ t := by
    intro j hj
    have hneq := (Finset.mem_filter.mp hj).2
    have hlt : j.val < mC η₀ D.n := by
      by_contra hnot
      have hge : mC η₀ D.n ≤ j.val := by omega
      exact hneq (D.keyOf_cubeFlip_eq_of_ge v j hge)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
  have hcard : t.card ≤ mC η₀ D.n := by
    let f : {j : Fin D.n // j.val < mC η₀ D.n} → Fin (mC η₀ D.n) :=
      fun j => ⟨j.1.val, j.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      exact Fin.ext (congrArg (fun x : Fin (mC η₀ D.n) => x.val) hab)
    have hc := Fintype.card_le_of_injective f hf
    have hsub : (Finset.univ.filter fun j : Fin D.n => j.val < mC η₀ D.n).card =
        Fintype.card {j : Fin D.n // j.val < mC η₀ D.n} := by
      simpa using (Finset.card_subtype (fun j : Fin D.n => j.val < mC η₀ D.n)
        (Finset.univ : Finset (Fin D.n))).symm
    simpa [t, hsub] using hc
  exact (Finset.card_le_card hst).trans hcard

theorem eventually_m_s_log_le_quarter (η : ℝ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (mC η n : ℝ) * sC η n * Real.log n ≤ (n : ℝ) / 4 := by
  have hlogEvent : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    have hsmall : (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
        fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
        tendsto_natCast_atTop_atTop
    have hnorm := hsmall.eventuallyLE
    filter_upwards [hnorm, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hnn
    have hlogpos : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hnn)
    have hpowpos : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have hnabs : |Real.log (n : ℝ)| ≤ |(n : ℝ) ^ (1 / 2 : ℝ)| := by
      simpa [Real.norm_eq_abs] using hn
    rw [abs_of_nonneg hlogpos, abs_of_nonneg hpowpos] at hnabs
    exact hnabs
  have hpowTend : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 20 : ℝ)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp tendsto_natCast_atTop_atTop
  have hpowEvent : ∀ᶠ n : ℕ in atTop, 16 ≤ (n : ℝ) ^ (1 / 20 : ℝ) :=
    hpowTend.eventually (Filter.eventually_ge_atTop (16 : ℝ))
  have hnEvent : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact_mod_cast hn
  have hLarge : ∀ᶠ n : ℕ in atTop,
      1 ≤ (n : ℝ) ∧ 16 ≤ (n : ℝ) ^ (1 / 20 : ℝ) ∧
        Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    filter_upwards [hnEvent, hpowEvent, hlogEvent] with n hn hp hl
    exact ⟨hn, hp, hl⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hLarge
  refine ⟨n₀, ?_⟩
  intro n hn
  have hlarge := hn₀ n hn
  let x : ℝ := n
  have hx1 : 1 ≤ x := hlarge.1
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have htau : tau8 η ≤ (1 / 100 : ℝ) := by
    calc
      tau8 η = eta8 η / 4 := tau8_eq η
      _ ≤ (4 / 100) / 4 := by
        exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      _ = 1 / 100 := by norm_num
  have hsCeil : (sC η n : ℝ) < x ^ tau8 η + 1 := by
    unfold sC
    exact_mod_cast (Nat.ceil_lt_add_one (by positivity : 0 ≤ x ^ tau8 η))
  have hsPow : x ^ tau8 η ≤ x ^ (1 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsOne : 1 ≤ x ^ (1 / 10 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hs : (sC η n : ℝ) ≤ 2 * x ^ (1 / 10 : ℝ) := by linarith
  have hlFloor : (lC n : ℝ) ≤ x ^ (1 / 5 : ℝ) := by
    unfold lC
    exact Nat.floor_le (by positivity : 0 ≤ x ^ (1 / 5 : ℝ))
  have hlPow : x ^ (1 / 5 : ℝ) ≤ x ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hl : (lC n : ℝ) ≤ x ^ (1 / 4 : ℝ) := hlFloor.trans hlPow
  have hms : (mC η n : ℝ) * sC η n ≤ 4 * x ^ (9 / 20 : ℝ) := by
    have hmul : (mC η n : ℝ) = (sC η n : ℝ) * (lC n : ℝ) := by
      simp [mC, Nat.cast_mul]
    rw [hmul]
    calc
      (sC η n : ℝ) * (lC n : ℝ) * sC η n ≤
          (2 * x ^ (1 / 10 : ℝ)) * x ^ (1 / 4 : ℝ) * (2 * x ^ (1 / 10 : ℝ)) := by
            gcongr
      _ = 4 * x ^ (9 / 20 : ℝ) := by
        have hconst : (2 * x ^ (1 / 10 : ℝ)) * x ^ (1 / 4 : ℝ) *
            (2 * x ^ (1 / 10 : ℝ)) =
            4 * (x ^ (1 / 10 : ℝ) * x ^ (1 / 4 : ℝ) * x ^ (1 / 10 : ℝ)) := by ring
        rw [hconst, ← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
        norm_num
  have hexp : x ^ (9 / 20 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (19 / 20 : ℝ) := by
    rw [← Real.rpow_add hxpos]
    norm_num
  have hpower : 4 * x ^ (19 / 20 : ℝ) ≤ x / 4 := by
    have hbig := hlarge.2.1
    have hx0 : 0 ≤ x := by linarith
    have hpownonneg : 0 ≤ x ^ (19 / 20 : ℝ) := Real.rpow_nonneg hx0 _
    have hmul := mul_le_mul_of_nonneg_left hbig hpownonneg
    have hsum : x ^ (19 / 20 : ℝ) * x ^ (1 / 20 : ℝ) = x := by
      rw [← Real.rpow_add hxpos]
      norm_num
    rw [hsum] at hmul
    nlinarith
  calc
    (mC η n : ℝ) * sC η n * Real.log n ≤
        (mC η n : ℝ) * sC η n * x ^ (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_left hlarge.2.2
          positivity
    _ ≤ (4 * x ^ (9 / 20 : ℝ)) * x ^ (1 / 2 : ℝ) := by
          gcongr
    _ = 4 * x ^ (19 / 20 : ℝ) := by
      have := congrArg (fun a : ℝ => 4 * a) hexp
      calc
        4 * x ^ (9 / 20 : ℝ) * x ^ (1 / 2 : ℝ) =
            4 * (x ^ (9 / 20 : ℝ) * x ^ (1 / 2 : ℝ)) := by ring
        _ = 4 * x ^ (19 / 20 : ℝ) := this
    _ ≤ x / 4 := hpower

theorem starLik_factor_le (hG : GridFacts η₀ D.n) (hP : D.PRowFacts)
    (q : D.Pre) (W : D.Anch) (v : CubeVertex D.n) (z : Fin D.N)
    (y : Fin D.n → Fin D.N) (j : Fin D.n) :
    D.prow q (Function.update W (cellOf η₀ v) z) (cellOf η₀ (cubeFlip v j)) (y j) ≤
      (if (cellOf η₀ (cubeFlip v j)).1 = (cellOf η₀ v).1 then
        (98 / 100 : ℝ)⁻¹ else
        Real.exp ((2 / 100 : ℝ) * sC η₀ D.n * Real.log D.n)) *
        D.refRow q W (cellOf η₀ v) (cellOf η₀ (cubeFlip v j)) (y j) := by
  classical
  let e : D.CellT := cellOf η₀ v
  let f : D.CellT := cellOf η₀ (cubeFlip v j)
  by_cases hk : f.1 = e.1
  · have hcross : ∀ u : D.CrossSub f.1, (u.1, f.2) ≠ e := by
      intro u heq
      have hfst : u.1 = f.1 := by
        calc
          u.1 = e.1 := congrArg Prod.fst heq
          _ = f.1 := hk.symm
      exact D.crossKey_ne_self f u hfst
    have hpv := D.presValid_update_eq q W e z f hcross
    have hp0 := D.p0_update_eq q W e z f hcross (y j)
    by_cases hv : D.Valid8 q (Function.update W e z) f
    · have hpres : D.PresValid q W f := by
        have hpres' := hv.1
        rw [hpv] at hpres'
        exact hpres'
      have href : D.refRow q W e f (y j) = D.p0 q W f (y j) := by
        simp [Ctx.refRow, e, f, hk, hpres]
      rcases hP q (Function.update W e z) f with ⟨_, _, hvalid⟩
      rcases hvalid hv with ⟨_, hrow, _⟩
      calc
        D.prow q (Function.update W e z) f (y j) ≤
            D.p0 q (Function.update W e z) f (y j) / (98 / 100 : ℝ) := hrow (y j)
        _ = (98 / 100 : ℝ)⁻¹ * D.p0 q W f (y j) := by
            rw [hp0, div_eq_mul_inv]
            ring
        _ = (if f.1 = e.1 then (98 / 100 : ℝ)⁻¹ else
              Real.exp ((2 / 100 : ℝ) * sC η₀ D.n * Real.log D.n)) *
              D.refRow q W e f (y j) := by
            rw [← href]
            simp [e, f, hk]
    · have hz : D.prow q (Function.update W e z) f (y j) = 0 := by
        simp [Ctx.prow, hv]
      rw [hz]
      have href0 := D.refRow_nonneg q W e f (y j)
      have hconst : 0 ≤ (98 / 100 : ℝ)⁻¹ := by positivity
      simpa [e, f, hk] using mul_nonneg hconst href0
  · have hN : 0 < D.N := by
      by_contra hnN
      have hN0 : D.N = 0 := Nat.eq_zero_of_not_pos hnN
      have hn : 1 ≤ D.n := hG.pos.1
      let i : Fin D.n := ⟨0, by omega⟩
      have hy : Fin D.N := y i
      rw [hN0] at hy
      exact Fin.elim0 hy
    have hNreal : 0 < (D.N : ℝ) := by exact_mod_cast hN
    by_cases hv : D.Valid8 q (Function.update W e z) f
    · rcases hP q (Function.update W e z) f with ⟨_, _, hvalid⟩
      rcases hvalid hv with ⟨_, _, hcap⟩
      have hmax := hcap (y j)
      have hdiv : D.prow q (Function.update W e z) f (y j) ≤
          Real.exp ((2 / 100 : ℝ) * sC η₀ D.n * Real.log D.n) / (D.N : ℝ) := by
        apply (le_div_iff₀ hNreal).2
        simpa [mul_comm] using hmax
      have href : D.refRow q W e f (y j) = (D.N : ℝ)⁻¹ := by
        simp [Ctx.refRow, e, f, hk]
      rw [if_neg hk]
      calc
        D.prow q (Function.update W e z) f (y j) ≤
            Real.exp ((2 / 100 : ℝ) * sC η₀ D.n * Real.log D.n) / (D.N : ℝ) := hdiv
        _ = Real.exp ((2 / 100 : ℝ) * sC η₀ D.n * Real.log D.n) *
              D.refRow q W e f (y j) := by rw [href, div_eq_mul_inv]
    · have hz : D.prow q (Function.update W e z) f (y j) = 0 := by
        simp [Ctx.prow, hv]
      rw [hz, if_neg hk]
      have href0 := D.refRow_nonneg q W e f (y j)
      simpa [e, f, hk] using mul_nonneg (Real.exp_pos _).le href0

noncomputable def crossCellEquiv (c : D.CellT) :
    D.CrossSub c.1 ≃ {t : D.CellT // t ∈ D.crossCells c} where
  toFun u := ⟨(u.1, c.2), Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩⟩
  invFun t := Classical.choose (Finset.mem_image.mp t.2)
  left_inv u := by
    apply Subtype.ext
    have hm : (u.1, c.2) ∈ D.crossCells c :=
      Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    have hs := Classical.choose_spec (Finset.mem_image.mp hm)
    exact congrArg Prod.fst hs.2
  right_inv t := by
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_image.mp t.2)).2

end Ctx

namespace Lane_q_s08_anchor

open Ctx

variable {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)

theorem finPerm_of_same_fiber_card {α : Type*} [Fintype α] [DecidableEq α]
    (f g : Fin D.n → α)
    (hf : ∀ a, Fintype.card {j : Fin D.n // f j = a} =
      Fintype.card {j : Fin D.n // g j = a}) :
    ∃ e : Fin D.n ≃ Fin D.n, ∀ j, f j = g (e j) := by
  classical
  let Ff := Equiv.sigmaFiberEquiv f
  let Fg := Equiv.sigmaFiberEquiv g
  let S := Equiv.sigmaCongrRight fun a => Fintype.equivOfCardEq (hf a)
  let e : Fin D.n ≃ Fin D.n := Ff.symm.trans (S.trans Fg)
  refine ⟨e, fun j => ?_⟩
  have hfbase : (Ff.symm j).1 = f j := by simp [Ff]
  have hgbase (x : Σ a : α, {j : Fin D.n // g j = a}) : g (Fg x) = x.1 := by
    rcases x with ⟨a, ⟨j, hj⟩⟩
    exact hj
  calc
    f j = (Ff.symm j).1 := hfbase.symm
    _ = (S (Ff.symm j)).1 := rfl
    _ = g (Fg (S (Ff.symm j))) := (hgbase _).symm
    _ = g (e j) := rfl

theorem alarmRate_eq_of_flipCellEquiv (q : D.Pre) (W : D.Anch)
    (v w : CubeVertex D.n) (e : Fin D.n ≃ Fin D.n)
    (hbase : cellOf η₀ v = cellOf η₀ w)
    (hcell : ∀ j, cellOf η₀ (cubeFlip v (e j)) = cellOf η₀ (cubeFlip w j)) :
    D.alarmRate q W v = D.alarmRate q W w := by
  classical
  let E : (Fin D.n → Fin D.N) ≃ (Fin D.n → Fin D.N) :=
    Equiv.piCongrLeft' (fun _ : Fin D.n => Fin D.N) e
  have hLik (z : Fin D.N) (y : Fin D.n → Fin D.N) :
      D.starLik q W v z (E y) = D.starLik q W w z y := by
    unfold Ctx.starLik
    apply Fintype.prod_equiv e.symm
    intro j
    have hc := hcell (e.symm j)
    have he := e.apply_symm_apply j
    simpa [E, he, hbase] using congrArg
      (fun c => D.prow q (Function.update W (cellOf η₀ v) z) c (y (e.symm j))) hc
  have hRef (y : Fin D.n → Fin D.N) :
      D.starRef q W v (E y) = D.starRef q W w y := by
    unfold Ctx.starRef
    apply Fintype.prod_equiv e.symm
    intro j
    have hc := hcell (e.symm j)
    have he := e.apply_symm_apply j
    simpa [E, he, hbase] using congrArg
      (fun c => D.refRow q W (cellOf η₀ v) c (y (e.symm j))) hc
  have hMarg (y : Fin D.n → Fin D.N) :
      D.starMarg q W v (E y) = D.starMarg q W w y := by
    unfold Ctx.starMarg
    rw [hbase]
    apply Finset.sum_congr rfl
    intro z hz
    exact congrArg (fun x => (D.Usel q (cellOf η₀ w)).w z * x) (hLik z y)
  have hFail (y : Fin D.n → Fin D.N) :
      D.PredFail q W v (E y) = D.PredFail q W w y := by
    unfold Ctx.PredFail
    rw [hMarg, hRef]
  unfold Ctx.alarmRate
  rw [← Equiv.sum_comp E]
  apply Finset.sum_congr rfl
  intro y hy
  have hprod :
      (∏ j, D.prow q W (cellOf η₀ (cubeFlip v j)) (E y j)) =
        ∏ j, D.prow q W (cellOf η₀ (cubeFlip w j)) (y j) := by
    apply Fintype.prod_equiv e.symm
    intro j
    have hc := hcell (e.symm j)
    have he := e.apply_symm_apply j
    simpa [E, he] using congrArg (fun c => D.prow q W c (y (e.symm j))) hc
  rw [hprod, hFail]

def specialKeyCount (v : CubeVertex D.n) (u : D.KeyT) : ℕ :=
  (Finset.univ.filter fun j : Fin D.n =>
    j.val < mC η₀ D.n ∧ keyOf η₀ (cubeFlip v j) = u).card

abbrev KeyProfileDomain (g : D.KeyT) := {u : D.KeyT // u ∈ insert g (crossKeys g)}

def keyProfile (v : CubeVertex D.n) (g : D.KeyT) :
    KeyProfileDomain D g → Fin (D.n + 1) := fun u =>
  ⟨specialKeyCount D v u.1, by
    unfold specialKeyCount
    have hle := Finset.card_filter_le (Finset.univ : Finset (Fin D.n))
      (fun j => j.val < mC η₀ D.n ∧ keyOf η₀ (cubeFlip v j) = u.1)
    have : (Finset.univ : Finset (Fin D.n)).card = D.n := by simp
    rw [this] at hle
    omega⟩

theorem resOf_flip_eq_self_of_special (v : CubeVertex D.n) (j : Fin D.n)
    (hm : mC η₀ D.n ≤ D.n) (hj : j.val < mC η₀ D.n) :
    resOf η₀ (cubeFlip v j) = resOf η₀ v := by
  funext k
  have hi : (⟨mC η₀ D.n + k.val, by
      have hk := k.isLt
      unfold dC at hk
      omega⟩ : Fin D.n) ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_mk] at hv
    omega
  simp [resOf, cubeFlip, hi]

theorem resOf_flip_eq_of_same_res (v w : CubeVertex D.n) (j : Fin D.n)
    (hres : resOf η₀ v = resOf η₀ w) :
    resOf η₀ (cubeFlip v j) = resOf η₀ (cubeFlip w j) := by
  funext k
  let i : Fin D.n := ⟨mC η₀ D.n + k.val, by
    have hk := k.isLt
    unfold dC at hk
    omega⟩
  have hvw := congrFun hres k
  change Function.update v j (!v j) i = Function.update w j (!w j) i
  by_cases hij : i = j
  · subst j
    have hvw' : v i = w i := by simpa [resOf, i] using hvw
    simp [cubeFlip, hvw']
  · rw [Function.update_of_ne hij, Function.update_of_ne hij]
    exact hvw

theorem flipCell_eq_of_sameCell_residual (hG : GridFacts η₀ D.n)
    (v w : CubeVertex D.n) (hbase : cellOf η₀ v = cellOf η₀ w)
    (j : Fin D.n) (hj : mC η₀ D.n ≤ j.val) :
  cellOf η₀ (cubeFlip v j) = cellOf η₀ (cubeFlip w j) := by
  apply Prod.ext
  · change keyOf η₀ (cubeFlip v j) = keyOf η₀ (cubeFlip w j)
    rw [D.keyOf_cubeFlip_eq_of_ge v j hj, D.keyOf_cubeFlip_eq_of_ge w j hj]
    exact congrArg Prod.fst hbase
  · exact resOf_flip_eq_of_same_res D v w j (congrArg Prod.snd hbase)

theorem specialFlipKey_mem_profile (hG : GridFacts η₀ D.n)
    (v : CubeVertex D.n) (c : D.CellT) (hvc : cellOf η₀ v = c)
    (j : Fin D.n) (hj : j.val < mC η₀ D.n) :
    keyOf η₀ (cubeFlip v j) = c.1 ∨ keyOf η₀ (cubeFlip v j) ∈ crossKeys c.1 := by
  have hPad := hG.edge v (cubeFlip v j) (cubeFlip_adj v j)
  cases hvc
  rcases hPad with ⟨hk, _⟩ | ⟨_, hk⟩
  · exact Or.inl hk
  · exact Or.inr hk

theorem specialKeyCount_eq_of_profile_eq (hG : GridFacts η₀ D.n)
    (v w : CubeVertex D.n) (c : D.CellT)
    (hvc : cellOf η₀ v = c) (hwc : cellOf η₀ w = c)
    (hp : keyProfile D v c.1 = keyProfile D w c.1) (u : D.KeyT) :
    specialKeyCount D v u = specialKeyCount D w u := by
  classical
  by_cases hu : u = c.1 ∨ u ∈ crossKeys c.1
  · let u' : KeyProfileDomain D c.1 := ⟨u, by simpa using hu⟩
    have heq := congrFun hp u'
    have := congrArg Fin.val heq
    simpa [keyProfile, specialKeyCount, u'] using this
  · have hzero (x : CubeVertex D.n) (hxc : cellOf η₀ x = c) :
      specialKeyCount D x u = 0 := by
      unfold specialKeyCount
      have hempty : (Finset.univ.filter fun j : Fin D.n =>
          j.val < mC η₀ D.n ∧ keyOf η₀ (cubeFlip x j) = u) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j hj
        rintro ⟨hj, hkey⟩
        exact hu (hkey ▸ specialFlipKey_mem_profile D hG x c hxc j hj)
      simp [hempty]
    rw [hzero v hvc, hzero w hwc]

theorem flipCell_fiber_card_eq_of_profile_eq (hG : GridFacts η₀ D.n)
    (v w : CubeVertex D.n) (c : D.CellT)
    (hvc : cellOf η₀ v = c) (hwc : cellOf η₀ w = c)
    (hp : keyProfile D v c.1 = keyProfile D w c.1) (t : D.CellT) :
    Fintype.card {j : Fin D.n // cellOf η₀ (cubeFlip v j) = t} =
      Fintype.card {j : Fin D.n // cellOf η₀ (cubeFlip w j) = t} := by
  classical
  let Fv : Finset (Fin D.n) := Finset.univ.filter
    fun j => cellOf η₀ (cubeFlip v j) = t
  let Fw : Finset (Fin D.n) := Finset.univ.filter
    fun j => cellOf η₀ (cubeFlip w j) = t
  let Sv := Fv.filter fun j => j.val < mC η₀ D.n
  let Sw := Fw.filter fun j => j.val < mC η₀ D.n
  let Rv := Fv.filter fun j => ¬ j.val < mC η₀ D.n
  let Rw := Fw.filter fun j => ¬ j.val < mC η₀ D.n
  have hm : mC η₀ D.n ≤ D.n := by
    have hs := hG.split
    omega
  have hresV (j : Fin D.n) (hj : j.val < mC η₀ D.n) :
      (cellOf η₀ (cubeFlip v j)).2 = c.2 := by
    change resOf η₀ (cubeFlip v j) = c.2
    rw [resOf_flip_eq_self_of_special D v j hm hj]
    exact congrArg Prod.snd hvc
  have hresW (j : Fin D.n) (hj : j.val < mC η₀ D.n) :
      (cellOf η₀ (cubeFlip w j)).2 = c.2 := by
    change resOf η₀ (cubeFlip w j) = c.2
    rw [resOf_flip_eq_self_of_special D w j hm hj]
    exact congrArg Prod.snd hwc
  have hS : Sv.card = Sw.card := by
    by_cases ht : t.2 = c.2
    · have hvSet : Sv = Finset.univ.filter fun j : Fin D.n =>
          j.val < mC η₀ D.n ∧ keyOf η₀ (cubeFlip v j) = t.1 := by
        ext j
        simp only [Sv, Fv, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hcell, hj⟩
          exact ⟨hj, congrArg Prod.fst hcell⟩
        · rintro ⟨hj, hkey⟩
          exact ⟨Prod.ext hkey ((hresV j hj).trans ht.symm), hj⟩
      have hwSet : Sw = Finset.univ.filter fun j : Fin D.n =>
          j.val < mC η₀ D.n ∧ keyOf η₀ (cubeFlip w j) = t.1 := by
        ext j
        simp only [Sw, Fw, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hcell, hj⟩
          exact ⟨hj, congrArg Prod.fst hcell⟩
        · rintro ⟨hj, hkey⟩
          exact ⟨Prod.ext hkey ((hresW j hj).trans ht.symm), hj⟩
      rw [hvSet, hwSet]
      exact specialKeyCount_eq_of_profile_eq D hG v w c hvc hwc hp t.1
    · have hvEmpty : Sv = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hjF, hj⟩
        have hcell := (Finset.mem_filter.mp hjF).2
        exact ht ((congrArg Prod.snd hcell).symm.trans (hresV j hj))
      have hwEmpty : Sw = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hjF, hj⟩
        have hcell := (Finset.mem_filter.mp hjF).2
        exact ht ((congrArg Prod.snd hcell).symm.trans (hresW j hj))
      rw [hvEmpty, hwEmpty]
  have hR : Rv = Rw := by
    ext j
    by_cases hj : j.val < mC η₀ D.n
    · simp [Rv, Rw, Fv, Fw, hj]
    · have hj' : mC η₀ D.n ≤ j.val := by omega
      have hflip := flipCell_eq_of_sameCell_residual D hG v w
        (hvc.trans hwc.symm) j hj'
      simp [Rv, Rw, Fv, Fw, hj, hflip]
  have hpartV : Fv.card = Sv.card + Rv.card := by
    simpa [Sv, Rv] using
      (Finset.card_filter_add_card_filter_not
        (s := Fv) (p := fun j : Fin D.n => j.val < mC η₀ D.n)).symm
  have hpartW : Fw.card = Sw.card + Rw.card := by
    simpa [Sw, Rw] using
      (Finset.card_filter_add_card_filter_not
        (s := Fw) (p := fun j : Fin D.n => j.val < mC η₀ D.n)).symm
  have hF : Fv.card = Fw.card := by
    rw [hpartV, hpartW, hS, hR]
  simpa [Fv, Fw, Fintype.card_subtype] using hF

def cellRoleProfiles (c : D.CellT) :
    Finset (KeyProfileDomain D c.1 → Fin (D.n + 1)) :=
  (Finset.univ.filter fun a : EvenRole D.n => cellOf η₀ a.1 = c).image
    (fun a => keyProfile D a.1 c.1)

theorem cellRoleProfiles_card_le (hG : GridFacts η₀ D.n) (c : D.CellT) :
    (cellRoleProfiles D c).card ≤ (D.n + 1) ^ (2 * sC η₀ D.n + 1) := by
  classical
  have hg : c.1 ∉ crossKeys c.1 := by
    simp [crossKeys, D.keyDist_self]
  have hdom : Fintype.card (KeyProfileDomain D c.1) =
      (insert c.1 (crossKeys c.1)).card := by
    calc
      Fintype.card (KeyProfileDomain D c.1) =
          (Finset.univ.filter fun u : D.KeyT =>
            u = c.1 ∨ u ∈ crossKeys c.1).card := by
              simp [KeyProfileDomain, Fintype.card_subtype]
      _ = (insert c.1 (crossKeys c.1)).card := by
            congr 1
            ext u
            simp [or_comm]
  have hdomle : Fintype.card (KeyProfileDomain D c.1) ≤ 2 * sC η₀ D.n + 1 := by
    rw [hdom, Finset.card_insert_of_notMem hg]
    exact Nat.add_le_add_right (hG.crossKeys_card c.1) 1
  have hPcard : Fintype.card (KeyProfileDomain D c.1 → Fin (D.n + 1)) ≤
      (D.n + 1) ^ (2 * sC η₀ D.n + 1) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_le_pow_right (by omega) hdomle
  calc
    (cellRoleProfiles D c).card ≤
        (Finset.univ : Finset (KeyProfileDomain D c.1 → Fin (D.n + 1))).card :=
      Finset.card_le_univ _
    _ = Fintype.card (KeyProfileDomain D c.1 → Fin (D.n + 1)) := by simp
    _ ≤ (D.n + 1) ^ (2 * sC η₀ D.n + 1) := hPcard

theorem alarmRate_eq_of_same_keyProfile (hG : GridFacts η₀ D.n)
    (q : D.Pre) (W : D.Anch) (v w : EvenRole D.n) (c : D.CellT)
    (hvc : cellOf η₀ v.1 = c) (hwc : cellOf η₀ w.1 = c)
    (hp : keyProfile D v.1 c.1 = keyProfile D w.1 c.1) :
    D.alarmRate q W v.1 = D.alarmRate q W w.1 := by
  classical
  let f : Fin D.n → D.CellT := fun j => cellOf η₀ (cubeFlip v.1 j)
  let g : Fin D.n → D.CellT := fun j => cellOf η₀ (cubeFlip w.1 j)
  obtain ⟨e, he⟩ := finPerm_of_same_fiber_card D f g (fun t => by
    exact flipCell_fiber_card_eq_of_profile_eq D hG v.1 w.1 c hvc hwc hp t)
  have hcell : ∀ j, cellOf η₀ (cubeFlip v.1 (e.symm j)) =
      cellOf η₀ (cubeFlip w.1 j) := by
    intro j
    have h := he (e.symm j)
    simpa [f, g, e.apply_symm_apply j] using h
  exact alarmRate_eq_of_flipCellEquiv D q W v.1 w.1 e.symm
    (hvc.trans hwc.symm) hcell

theorem prow_nonneg (q : D.Pre) (W : D.Anch) (c : D.CellT) (y : Fin D.N) :
    0 ≤ D.prow q W c y := by
  unfold Ctx.prow
  by_cases hv : D.Valid8 q W c
  · simp only [hv, ↓reduceIte]
    have hr : 0 < D.ordRet q W c := by
      rcases hv with ⟨_, hv⟩
      have hpos : (0 : ℝ) < 98 / 100 := by norm_num
      exact lt_of_lt_of_le hpos hv
    apply div_nonneg
    · apply mul_nonneg (D.p0_nonneg q W c y)
      split_ifs <;> norm_num
    · exact hr.le
  · simp [hv]

theorem alarmRate_nonneg (q : D.Pre) (W : D.Anch) (v : CubeVertex D.n) :
    0 ≤ D.alarmRate q W v := by
  unfold Ctx.alarmRate
  apply Finset.sum_nonneg
  intro y hy
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro j hj
    exact prow_nonneg D q W (cellOf η₀ (cubeFlip v j)) (y j)
  · exact ind_nonneg _

theorem alarmRate_tail (hA : D.AlarmMean) (q : D.Pre) (W : D.Anch)
    (a : EvenRole D.n) (c : D.CellT) (hca : cellOf η₀ a.1 = c) :
    ∑ z, (D.Usel q c).w z *
      (if Real.exp (-(2 / 100 : ℝ) * D.n) <
          D.alarmRate q (Function.update W c z) a.1 then 1 else 0) ≤
        Real.exp (-(2 / 100 : ℝ) * D.n) := by
  classical
  cases hca
  let t : ℝ := Real.exp (-(2 / 100 : ℝ) * D.n)
  have ht : 0 < t := by positivity
  have hpoint (z : Fin D.N) : t *
      (if t < D.alarmRate q (Function.update W (cellOf η₀ a.1) z) a.1 then 1 else 0) ≤
        D.alarmRate q (Function.update W (cellOf η₀ a.1) z) a.1 := by
    by_cases hz : t < D.alarmRate q (Function.update W (cellOf η₀ a.1) z) a.1
    · simpa [hz] using le_of_lt hz
    · simp only [hz, ↓reduceIte, mul_zero]
      exact alarmRate_nonneg D q (Function.update W (cellOf η₀ a.1) z) a.1
  have hmarkov : t *
      (∑ z, (D.Usel q (cellOf η₀ a.1)).w z *
        (if t < D.alarmRate q (Function.update W (cellOf η₀ a.1) z) a.1 then 1 else 0)) ≤
      Real.exp (-(4 / 100 : ℝ) * D.n) := by
    calc
      _ = ∑ z, (D.Usel q (cellOf η₀ a.1)).w z *
          (t * (if t < D.alarmRate q (Function.update W (cellOf η₀ a.1) z) a.1 then 1 else 0)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z hz
            ring
      _ ≤ ∑ z, (D.Usel q (cellOf η₀ a.1)).w z *
          D.alarmRate q (Function.update W (cellOf η₀ a.1) z) a.1 := by
            apply Finset.sum_le_sum
            intro z hz
            exact mul_le_mul_of_nonneg_left (hpoint z)
              ((D.Usel q (cellOf η₀ a.1)).nonneg z)
      _ ≤ Real.exp (-(4 / 100 : ℝ) * D.n) := hA q W a
  have hmarkov' :
      (∑ z, (D.Usel q (cellOf η₀ a.1)).w z *
        (if t < D.alarmRate q (Function.update W (cellOf η₀ a.1) z) a.1 then 1 else 0)) * t ≤
      Real.exp (-(4 / 100 : ℝ) * D.n) := by
    simpa [mul_comm] using hmarkov
  have hdiv :
      (∑ z, (D.Usel q (cellOf η₀ a.1)).w z *
        (if t < D.alarmRate q (Function.update W (cellOf η₀ a.1) z) a.1 then 1 else 0)) ≤
      Real.exp (-(4 / 100 : ℝ) * D.n) / t := (le_div_iff₀ ht).2 hmarkov'
  have hexp : Real.exp (-(4 / 100 : ℝ) * D.n) / t = t := by
    dsimp [t]
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hexp] at hdiv
  simpa [t] using hdiv

theorem pi_pr_le_of_update_coordinate_bound {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] (P : ι → FinProb Ω) (i : ι) (F : (ι → Ω) → Prop) (B : ℝ)
    (hpoint : ∀ W, ∑ z, (P i).w z *
      (if F (Function.update W i z) then 1 else 0) ≤ B) :
    (FinProb.pi P).pr F ≤ B := by
  classical
  let S : Finset ι := {i}
  let ACoord := {j : ι // j ∈ S}
  let BCoord := {j : ι // j ∉ S}
  let PA : FinProb (ACoord → Ω) := FinProb.pi fun t => P t.1
  let PB : FinProb (BCoord → Ω) := FinProb.pi fun t => P t.1
  let splitEquiv := Equiv.piEquivPiSubtypeProd (fun j : ι => j ∈ S) (fun _ => Ω)
  let ti : ACoord := ⟨i, by simp [S]⟩
  let EA : (ACoord → Ω) ≃ Ω := {
    toFun := fun a : ACoord → Ω => a ti
    invFun := fun z : Ω => fun _ : ACoord => z
    left_inv := fun a => by
      funext t
      have ht : t = ti := by
        apply Subtype.ext
        exact Finset.mem_singleton.mp (by simpa [S] using t.2)
      subst t
      rfl
    right_inv := fun z => rfl }
  let Wbase : Ω := Classical.choice (finProb_nonempty (P i))
  let Wout (b : BCoord → Ω) : ι → Ω := fun j =>
    if hj : j ∈ S then Wbase else b ⟨j, hj⟩
  let whole (a : ACoord → Ω) (b : BCoord → Ω) : ι → Ω := splitEquiv.symm (a, b)
  have hwhole (a : ACoord → Ω) (b : BCoord → Ω) :
      whole a b = Function.update (Wout b) i (EA a) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [whole, splitEquiv, Wout, EA, ti, S,
        Equiv.piEquivPiSubtypeProd_symm_apply]
    · simp [whole, splitEquiv, Wout, EA, ti, S, hj,
        Equiv.piEquivPiSubtypeProd_symm_apply]
  have hPAw (a : ACoord → Ω) : PA.w a = (P i).w (EA a) := by
    letI : Unique ACoord := ⟨⟨ti⟩, fun t => by
      apply Subtype.ext
      exact Finset.mem_singleton.mp (by simpa [S] using t.2)⟩
    have hdefault : (default : ACoord) = ti := rfl
    simp [PA, FinProb.pi, EA, ti, hdefault]
  let Indicator : (ι → Ω) → ℝ := fun W => if F W then 1 else 0
  have hind : (FinProb.pi P).pr F = (FinProb.pi P).expect Indicator := by
    unfold FinProb.pr FinProb.expect Indicator
    apply Finset.sum_congr rfl
    intro W hW
    by_cases hF : F W <;> simp [hF]
  have hsplit : (FinProb.pi P).pr F =
      ∑ a : ACoord → Ω, ∑ b : BCoord → Ω,
        PA.w a * PB.w b * Indicator (whole a b) := by
    rw [hind]
    simpa [PA, PB, Indicator, whole, splitEquiv, S] using
      (pi_expect_split_full (fun j : ι => P j) S Indicator)
  have hinner (b : BCoord → Ω) :
      ∑ a : ACoord → Ω, PA.w a * Indicator (whole a b) ≤ B := by
    rw [← Equiv.sum_comp EA.symm]
    calc
      (∑ z : Ω, PA.w (EA.symm z) * Indicator (whole (EA.symm z) b)) =
          ∑ z : Ω, (P i).w z * (if F (Function.update (Wout b) i z) then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [hPAw, hwhole]
            simp [Indicator]
      _ ≤ B := hpoint (Wout b)
  have houter :
      (∑ a : ACoord → Ω, ∑ b : BCoord → Ω,
        PA.w a * PB.w b * Indicator (whole a b)) =
      ∑ b : BCoord → Ω, PB.w b * ∑ a : ACoord → Ω, PA.w a * Indicator (whole a b) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    calc
      (∑ a : ACoord → Ω, PA.w a * PB.w b * Indicator (whole a b)) =
          ∑ a, PB.w b * (PA.w a * Indicator (whole a b)) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
      _ = PB.w b * ∑ a : ACoord → Ω, PA.w a * Indicator (whole a b) := by
            rw [← Finset.mul_sum]
  calc
    (FinProb.pi P).pr F =
        ∑ b : BCoord → Ω, PB.w b * ∑ a : ACoord → Ω, PA.w a * Indicator (whole a b) := by
          rw [hsplit, houter]
    _ ≤ ∑ b : BCoord → Ω, PB.w b * B := by
          apply Finset.sum_le_sum
          intro b hb
          exact mul_le_mul_of_nonneg_left (hinner b) (PB.nonneg b)
    _ = B := by
          calc
            (∑ b : BCoord → Ω, PB.w b * B) = (∑ b : BCoord → Ω, PB.w b) * B := by
              rw [← Finset.sum_mul]
            _ = B := by rw [PB.sum_eq_one, one_mul]

private theorem eventually_rpow_dominates {a b C : ℝ} (hab : a < b) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually (eventually_ge_atTop C),
    Filter.eventually_gt_atTop (1 : ℕ)] with n hn hN
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hmul := mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hnpos.le a)
  have hident : (n : ℝ) ^ a * (n : ℝ) ^ (b - a) = (n : ℝ) ^ b := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  calc
    C * (n : ℝ) ^ a ≤ (n : ℝ) ^ a * (n : ℝ) ^ (b - a) := by
      simpa [mul_comm] using hmul
    _ = (n : ℝ) ^ b := hident

private theorem eventually_exp_neg_rpow_le {r A M : ℝ} (hr : 0 < r) (hA : 0 < A) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-A * (n : ℝ) ^ r) ≤ (n : ℝ) ^ (-M) := by
  let b : ℝ := -M / r
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ r) atTop atTop :=
    (_root_.tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop
  have hlittle := hpow.eventually (isLittleO_exp_neg_mul_rpow_atTop hA b).eventuallyLE
  filter_upwards [hlittle, Filter.eventually_gt_atTop (1 : ℕ)] with n hn hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
  have hargpos : 0 < (n : ℝ) ^ r := Real.rpow_pos_of_pos hnpos r
  have hval : |Real.exp (-A * (n : ℝ) ^ r)| ≤ |((n : ℝ) ^ r) ^ b| := by
    simpa [Real.norm_eq_abs] using hn
  rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.rpow_pos_of_pos hargpos b)] at hval
  have hident : ((n : ℝ) ^ r) ^ b = (n : ℝ) ^ (-M) := by
    rw [← Real.rpow_mul hnpos.le r b]
    congr 1
    dsimp [b]
    field_simp [ne_of_gt hr]
  rw [hident] at hval
  exact hval

private theorem eventually_sC_le_two_rpow_tenth (η : ℝ) :
    ∀ᶠ n : ℕ in atTop, (sC η n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 10 : ℝ) := by
  have htau : tau8 η ≤ (1 / 100 : ℝ) := by
    calc
      tau8 η = eta8 η / 4 := tau8_eq η
      _ ≤ (4 / 100) / 4 := by
        exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
      _ = 1 / 100 := by norm_num
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  let x : ℝ := n
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast hn
  have hsCeil : (sC η n : ℝ) < x ^ tau8 η + 1 := by
    unfold sC
    exact_mod_cast (Nat.ceil_lt_add_one (by positivity : 0 ≤ x ^ tau8 η))
  have hsPow : x ^ tau8 η ≤ x ^ (1 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsOne : 1 ≤ x ^ (1 / 10 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hs : (sC η n : ℝ) ≤ 2 * x ^ (1 / 10 : ℝ) := by linarith
  simpa [x] using hs

private theorem eventually_log_nat_add_one_le_two_rpow_half :
    ∀ᶠ n : ℕ in atTop, Real.log ((n : ℝ) + 1) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hsmall := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have harg : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hsmall' := harg.eventually hsmall.eventuallyLE
  filter_upwards [hsmall', Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
  have hnge : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hpowpos : 0 ≤ ((n : ℝ) + 1) ^ (1 / 2 : ℝ) := by positivity
  have habs : |Real.log ((n : ℝ) + 1)| ≤ |((n : ℝ) + 1) ^ (1 / 2 : ℝ)| := by
    simpa [Real.norm_eq_abs] using hn
  rw [abs_of_nonneg hlog, abs_of_nonneg hpowpos] at habs
  have hbase : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
  have hpow : ((n : ℝ) + 1) ^ (1 / 2 : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    have hle := Real.rpow_le_rpow (by positivity : 0 ≤ (n : ℝ) + 1) hbase (by norm_num : 0 ≤ (1 / 2 : ℝ))
    have htwo : (2 * (n : ℝ)) ^ (1 / 2 : ℝ) =
        (2 : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
    have htwo' : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      have : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      simpa using this
    rw [htwo] at hle
    exact hle.trans (mul_le_mul_of_nonneg_right htwo' (by positivity))
  exact habs.trans hpow

private theorem sqrt_exp_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  congr 1
  ring

theorem sqrt_sqrt_exp_neg (x : ℝ) :
    Real.sqrt (Real.sqrt (Real.exp (-x))) = Real.exp (-x / 4) := by
  calc
    Real.sqrt (Real.sqrt (Real.exp (-x))) = Real.sqrt (Real.exp (-x / 2)) := by
      rw [sqrt_exp_half]
    _ = Real.exp (-x / 4) := by rw [sqrt_exp_half]; congr 1 <;> ring

set_option maxHeartbeats 1000000 in
theorem anchorLLL_asymptotic {β : ℝ} (η p : ℝ) (h : ℕ)
    (hη : 0 < η) (hp : 0 < p) (hh : 1 ≤ h) :
    ∃ cA > (0 : ℝ), ∃ n₀ : ℕ, ∀ D : Ctx η β p h, n₀ ≤ D.n → GridFacts η D.n →
      Real.sqrt (Real.sqrt D.eps0) +
        50 * ((D.n : ℝ) + 1) * D.Δ / (1 - D.Δ) +
        ((D.n : ℝ) + 1) ^ (2 * sC η D.n + 1) *
          Real.exp (-(2 / 100 : ℝ) * D.n) ≤ Real.exp (-((D.n : ℝ) ^ cA)) ∧
      (2 * sC η D.n + dC η D.n + 1) ^ 4 *
        (2 * Real.exp (-((D.n : ℝ) ^ cA))) ≤ 1 / 2 ∧
      Real.exp (-((D.n : ℝ) ^ cA)) < 1 / 2 := by
  let cA : ℝ := min (tau8 η / 100) (min (p / 100) (1 / 100))
  have htau : 0 < tau8 η := by rw [tau8_eq]; unfold eta8; positivity
  have hcA : 0 < cA := by dsimp [cA]; positivity
  have hcTau : cA < tau8 η := by
    dsimp [cA]
    exact (min_le_left _ _).trans_lt (div_lt_self htau (by norm_num))
  have hcP : cA < p / 2 := by
    dsimp [cA]
    have hpdiv : p / 100 < p / 2 := by nlinarith [hp]
    exact (le_trans (min_le_right _ _) (min_le_left _ _)).trans_lt hpdiv
  have hcOne : cA < 1 := by
    dsimp [cA]
    exact (le_trans (min_le_right _ _) (min_le_right _ _)).trans_lt (by norm_num)

  have hpowOne := eventually_rpow_dominates (a := cA) (b := tau8 η) (C := 160000)
    hcTau (by norm_num)
  have hpowTwo := eventually_rpow_dominates (a := cA) (b := p / 2) (C := 8)
    hcP (by norm_num)
  have hpowAlarm := eventually_rpow_dominates (a := cA) (b := 1) (C := 400)
    hcOne (by norm_num)
  have hpowPoly := eventually_rpow_dominates (a := (3 / 5 : ℝ)) (b := 1) (C := 1000)
    (by norm_num) (by norm_num)
  have hpowQ := eventually_rpow_dominates (a := (1 : ℝ)) (b := 3) (C := 800)
    (by norm_num) (by norm_num)
  have hSUpper := eventually_sC_le_two_rpow_tenth η
  have hLogUpper := eventually_log_nat_add_one_le_two_rpow_half
  have hlogT : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLogLower := hlogT.eventually (eventually_ge_atTop (1 : ℝ))
  have hTail := eventually_exp_neg_rpow_le (r := cA) (A := 3) (M := 1) hcA (by norm_num)
  have hDelta := eventually_exp_neg_rpow_le (r := p / 2) (A := 1) (M := 1)
    (by positivity) (by norm_num)
  have hQExp := eventually_exp_neg_rpow_le (r := p / 2) (A := 1 / 2) (M := 3)
    (by positivity) (by norm_num)
  have hChargeExp := eventually_exp_neg_rpow_le (r := cA) (A := 1) (M := 8)
    hcA (by norm_num)
  have hCAtop : Tendsto (fun n : ℕ => (n : ℝ) ^ cA) atTop atTop :=
    (_root_.tendsto_rpow_atTop hcA).comp tendsto_natCast_atTop_atTop
  have hCAGe2 := hCAtop.eventually (eventually_ge_atTop (2 : ℝ))

  have hprob : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (Real.sqrt (Real.exp (-((1 / 10000 : ℝ) * h * sC η n * Real.log n)))) +
        50 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) ^ (p / 2))) /
          (1 - Real.exp (-((n : ℝ) ^ (p / 2)))) +
        ((n : ℝ) + 1) ^ (2 * sC η n + 1) *
          Real.exp (-(2 / 100 : ℝ) * n) ≤ Real.exp (-((n : ℝ) ^ cA)) := by
    filter_upwards [hpowOne, hpowTwo, hpowAlarm, hpowPoly, hpowQ, hSUpper, hLogUpper,
      hLogLower, hTail, hDelta, hQExp, Filter.eventually_ge_atTop (4 : ℕ)]
      with n hOne hTwo hAlarm hPoly hQ hsu hlu hll htail hdelta hqexp hn4
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt (by omega : 1 < n))
    have hnge : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hNpos : 0 ≤ (n : ℝ) ^ (p / 2) := by positivity
    have hsLower : (n : ℝ) ^ tau8 η ≤ (sC η n : ℝ) := by
      unfold sC
      exact_mod_cast (Nat.le_ceil ((n : ℝ) ^ tau8 η))
    have hbase : (n : ℝ) ^ tau8 η ≤ (h : ℝ) * (sC η n : ℝ) * Real.log n := by
      have hhR : 1 ≤ (h : ℝ) := by exact_mod_cast hh
      have hlog : 1 ≤ Real.log (n : ℝ) := hll
      have hs0 : 0 ≤ (sC η n : ℝ) := by positivity
      have ht0 : 0 ≤ (n : ℝ) ^ tau8 η := by positivity
      calc
        (n : ℝ) ^ tau8 η ≤ (sC η n : ℝ) := hsLower
        _ ≤ (h : ℝ) * (sC η n : ℝ) := by nlinarith
        _ ≤ (h : ℝ) * (sC η n : ℝ) * Real.log n := by
          have hmul := mul_le_mul_of_nonneg_left hlog
            (mul_nonneg (by positivity : 0 ≤ (h : ℝ)) hs0)
          simpa using hmul
    have hcoef : 4 * (n : ℝ) ^ cA ≤
        ((1 / 10000 : ℝ) * h * (sC η n : ℝ) * Real.log n) / 4 := by
      have h1 := hOne
      have h2 : 160000 * (n : ℝ) ^ cA ≤ (n : ℝ) ^ tau8 η := h1
      nlinarith [hbase]
    have hfirst :
        Real.sqrt (Real.sqrt (Real.exp (-((1 / 10000 : ℝ) * h * sC η n * Real.log n)))) ≤
          (1 / 4 : ℝ) * Real.exp (-((n : ℝ) ^ cA)) := by
      rw [sqrt_sqrt_exp_neg]
      have hexp : Real.exp (-((1 / 10000 : ℝ) * h * (sC η n : ℝ) * Real.log n) / 4) ≤
          Real.exp (-4 * (n : ℝ) ^ cA) := Real.exp_le_exp.mpr (by linarith [hcoef])
      have htail' : Real.exp (-3 * (n : ℝ) ^ cA) ≤ 1 / 4 := by
        have h := htail
        have hinv : (n : ℝ) ^ (-1 : ℝ) ≤ (1 / 4 : ℝ) := by
          rw [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ)), Real.rpow_one]
          simpa [one_div] using
            (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
              (by exact_mod_cast (show 4 ≤ n by omega)))
        exact h.trans hinv
      calc
        Real.exp (-((1 / 10000 : ℝ) * h * (sC η n : ℝ) * Real.log n) / 4) ≤
            Real.exp (-4 * (n : ℝ) ^ cA) := hexp
        _ = Real.exp (-((n : ℝ) ^ cA)) * Real.exp (-3 * (n : ℝ) ^ cA) := by
            rw [← Real.exp_add]
            congr 1
            ring
        _ ≤ (1 / 4 : ℝ) * Real.exp (-((n : ℝ) ^ cA)) := by
            simpa [mul_comm] using mul_le_mul_of_nonneg_left htail' (Real.exp_nonneg (-((n : ℝ) ^ cA)))
    have hdeltaHalf : Real.exp (-((n : ℝ) ^ (p / 2))) ≤ 1 / 2 := by
      have h := hdelta
      have hinv : (n : ℝ) ^ (-1 : ℝ) ≤ (1 / 2 : ℝ) := by
        rw [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ)), Real.rpow_one]
        simpa [one_div] using
          (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
            (by exact_mod_cast (show 2 ≤ n by omega)))
      simpa using h.trans hinv
    have hqSmall : 100 * ((n : ℝ) + 1) *
        Real.exp (-((n : ℝ) ^ (p / 2)) / 2) ≤ 1 / 4 := by
      have hQn := hQ
      have hqpow := hqexp
      have hqpow' : Real.exp (-((n : ℝ) ^ (p / 2)) / 2) ≤ (n : ℝ) ^ (-3 : ℝ) := by
        have heq : -((n : ℝ) ^ (p / 2)) / 2 = -(1 / 2 : ℝ) * (n : ℝ) ^ (p / 2) := by ring
        simpa [heq] using hqpow
      have hQn' : 800 * (n : ℝ) ≤ (n : ℝ) ^ 3 := by simpa [Real.rpow_one] using hQn
      have hnplus : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith [hnge]
      have hpowid : (n : ℝ) ^ (-3 : ℝ) = 1 / (n : ℝ) ^ 3 := by
        rw [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ))]
        rw [← Real.rpow_natCast]
        simp [one_div]
      have hcoef : 100 * ((n : ℝ) + 1) ≤ 200 * (n : ℝ) := by nlinarith [hnge]
      have hsmallDen : 100 * ((n : ℝ) + 1) * (n : ℝ) ^ (-3 : ℝ) ≤ 1 / 4 := by
        calc
          _ ≤ 200 * (n : ℝ) * (n : ℝ) ^ (-3 : ℝ) :=
            mul_le_mul_of_nonneg_right hcoef (by positivity)
          _ = 200 * (n : ℝ) / (n : ℝ) ^ 3 := by rw [hpowid]; ring
          _ ≤ 1 / 4 := by
            have hden : 0 < (n : ℝ) ^ 3 := by positivity
            rw [div_le_iff₀ hden]
            calc
              200 * (n : ℝ) = 800 * (n : ℝ) / 4 := by ring
              _ ≤ (n : ℝ) ^ 3 / 4 := div_le_div_of_nonneg_right hQn' (by norm_num)
              _ = (1 / 4 : ℝ) * (n : ℝ) ^ 3 := by ring
      calc
        100 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) ^ (p / 2)) / 2) ≤
            100 * ((n : ℝ) + 1) * (n : ℝ) ^ (-3 : ℝ) :=
              mul_le_mul_of_nonneg_left hqpow' (by positivity)
        _ ≤ 1 / 4 := hsmallDen
    have hqLarge : 4 * (n : ℝ) ^ cA ≤ (n : ℝ) ^ (p / 2) / 2 := by
      have h := hTwo
      nlinarith [h]
    have hsecond :
        50 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) ^ (p / 2))) /
          (1 - Real.exp (-((n : ℝ) ^ (p / 2)))) ≤
          (1 / 4 : ℝ) * Real.exp (-((n : ℝ) ^ cA)) := by
      have hexpSplit : Real.exp (-((n : ℝ) ^ (p / 2))) =
          Real.exp (-((n : ℝ) ^ (p / 2)) / 2) *
            Real.exp (-((n : ℝ) ^ (p / 2)) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hterm : 100 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) ^ (p / 2))) ≤
          (1 / 4 : ℝ) * Real.exp (-4 * (n : ℝ) ^ cA) := by
        rw [hexpSplit]
        have hmono : Real.exp (-((n : ℝ) ^ (p / 2)) / 2) ≤
            Real.exp (-4 * (n : ℝ) ^ cA) := Real.exp_le_exp.mpr (by linarith [hqLarge])
        calc
          100 * ((n : ℝ) + 1) *
              (Real.exp (-((n : ℝ) ^ (p / 2)) / 2) * Real.exp (-((n : ℝ) ^ (p / 2)) / 2)) =
              (100 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) ^ (p / 2)) / 2)) *
                Real.exp (-((n : ℝ) ^ (p / 2)) / 2) := by ring
          _ ≤ (100 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) ^ (p / 2)) / 2)) *
                Real.exp (-4 * (n : ℝ) ^ cA) :=
                  mul_le_mul_of_nonneg_left hmono (by positivity)
          _ ≤ (1 / 4 : ℝ) * Real.exp (-4 * (n : ℝ) ^ cA) :=
                mul_le_mul_of_nonneg_right hqSmall (Real.exp_nonneg _)
      calc
        50 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) ^ (p / 2))) /
            (1 - Real.exp (-((n : ℝ) ^ (p / 2)))) ≤
            100 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) ^ (p / 2))) := by
              have hden : 0 < 1 - Real.exp (-((n : ℝ) ^ (p / 2))) := by
                linarith [hdeltaHalf]
              apply (div_le_iff₀ hden).2
              have hdenhalf : (1 / 2 : ℝ) ≤
                  1 - Real.exp (-((n : ℝ) ^ (p / 2))) := by linarith [hdeltaHalf]
              have hcoef0 : 0 ≤ 100 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) ^ (p / 2))) := by positivity
              have hmul := mul_le_mul_of_nonneg_left hdenhalf hcoef0
              nlinarith [hmul]
        _ ≤ (1 / 4 : ℝ) * Real.exp (-4 * (n : ℝ) ^ cA) := hterm
        _ ≤ (1 / 4 : ℝ) * Real.exp (-((n : ℝ) ^ cA)) := by
              have hexpMono : Real.exp (-4 * (n : ℝ) ^ cA) ≤ Real.exp (-((n : ℝ) ^ cA)) :=
                Real.exp_le_exp.mpr (by nlinarith [Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) cA])
              exact mul_le_mul_of_nonneg_left hexpMono (by norm_num)
    have hlogbound : ((2 * sC η n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) ≤
        (1 / 100 : ℝ) * (n : ℝ) := by
      have hn10 : 1 ≤ (n : ℝ) ^ (1 / 10 : ℝ) := Real.one_le_rpow hnge (by norm_num)
      have hlogadd0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith [hnge])
      have hk : ((2 * sC η n + 1 : ℕ) : ℝ) ≤ 5 * (n : ℝ) ^ (1 / 10 : ℝ) := by
        have hs := hsu
        norm_num at hs ⊢
        nlinarith [hn10]
      have hlog := hlu
      have hprod : ((2 * sC η n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) ≤
          10 * (n : ℝ) ^ (3 / 5 : ℝ) := by
        calc
          _ ≤ (5 * (n : ℝ) ^ (1 / 10 : ℝ)) *
              (2 * (n : ℝ) ^ (1 / 2 : ℝ)) := by
                exact mul_le_mul hk hlu hlogadd0 (by positivity)
          _ = 10 * ((n : ℝ) ^ (1 / 10 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) := by ring
          _ = 10 * (n : ℝ) ^ (3 / 5 : ℝ) := by
              rw [← Real.rpow_add hnpos]
              congr 1
              ring
      have hP : 1000 * (n : ℝ) ^ (3 / 5 : ℝ) ≤ (n : ℝ) := by
        simpa [Real.rpow_one] using hPoly
      have hP' : 10 * (n : ℝ) ^ (3 / 5 : ℝ) ≤ (1 / 100 : ℝ) * (n : ℝ) := by
        calc
          10 * (n : ℝ) ^ (3 / 5 : ℝ) = 1000 * (n : ℝ) ^ (3 / 5 : ℝ) / 100 := by ring
          _ ≤ (n : ℝ) / 100 := div_le_div_of_nonneg_right hP (by norm_num)
          _ = (1 / 100 : ℝ) * (n : ℝ) := by ring
      exact hprod.trans hP'
    have hpowerExp : ((n : ℝ) + 1) ^ (2 * sC η n + 1) =
        Real.exp (((2 * sC η n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
      ring
    have halarmExp : ((n : ℝ) + 1) ^ (2 * sC η n + 1) *
        Real.exp (-(2 / 100 : ℝ) * n) ≤ Real.exp (-4 * (n : ℝ) ^ cA) := by
      rw [hpowerExp, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hAlarm' : 400 * (n : ℝ) ^ cA ≤ (n : ℝ) := by simpa [Real.rpow_one] using hAlarm
      have hAlarm'' : 4 * (n : ℝ) ^ cA ≤ (1 / 100 : ℝ) * (n : ℝ) := by
        calc
          4 * (n : ℝ) ^ cA = (1 / 100 : ℝ) * (400 * (n : ℝ) ^ cA) := by ring
          _ ≤ (1 / 100 : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left hAlarm' (by norm_num)
      have harg : ((2 * sC η n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
          (-(2 / 100 : ℝ) * (n : ℝ)) ≤ -4 * (n : ℝ) ^ cA := by
        calc
          _ ≤ (1 / 100 : ℝ) * (n : ℝ) + (-(2 / 100 : ℝ) * (n : ℝ)) := by
            exact add_le_add_left hlogbound _
          _ = -(1 / 100 : ℝ) * (n : ℝ) := by ring
          _ ≤ -4 * (n : ℝ) ^ cA := by
            simpa [mul_assoc] using neg_le_neg hAlarm''
      exact harg
    have halarm : ((n : ℝ) + 1) ^ (2 * sC η n + 1) *
        Real.exp (-(2 / 100 : ℝ) * n) ≤
          (1 / 4 : ℝ) * Real.exp (-((n : ℝ) ^ cA)) := by
      calc
        _ ≤ Real.exp (-4 * (n : ℝ) ^ cA) := halarmExp
        _ = Real.exp (-((n : ℝ) ^ cA)) * Real.exp (-3 * (n : ℝ) ^ cA) := by
            rw [← Real.exp_add]
            congr 1
            ring
        _ ≤ (1 / 4 : ℝ) * Real.exp (-((n : ℝ) ^ cA)) := by
            have h := htail
            have hinv : (n : ℝ) ^ (-1 : ℝ) ≤ (1 / 4 : ℝ) := by
              rw [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ)), Real.rpow_one]
              simpa [one_div] using
                (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
                  (by exact_mod_cast (show 4 ≤ n by omega)))
            calc
              _ ≤ Real.exp (-((n : ℝ) ^ cA)) * (1 / 4 : ℝ) :=
                mul_le_mul_of_nonneg_left (h.trans hinv) (Real.exp_nonneg _)
              _ = (1 / 4 : ℝ) * Real.exp (-((n : ℝ) ^ cA)) := by ring
    have hsum :
        Real.sqrt (Real.sqrt (Real.exp (-((1 / 10000 : ℝ) * h * sC η n * Real.log n)))) +
          50 * ((n : ℝ) + 1) * Real.exp (-((n : ℝ) ^ (p / 2))) /
            (1 - Real.exp (-((n : ℝ) ^ (p / 2)))) +
          ((n : ℝ) + 1) ^ (2 * sC η n + 1) * Real.exp (-(2 / 100 : ℝ) * n) ≤
            Real.exp (-((n : ℝ) ^ cA) : ℝ) := by
      calc
        _ ≤ (1 / 4 : ℝ) * Real.exp (-((n : ℝ) ^ cA)) +
            (1 / 4 : ℝ) * Real.exp (-((n : ℝ) ^ cA)) +
            (1 / 4 : ℝ) * Real.exp (-((n : ℝ) ^ cA)) :=
              add_le_add (add_le_add hfirst hsecond) halarm
      _ ≤ Real.exp (-((n : ℝ) ^ cA)) := by nlinarith [Real.exp_nonneg (-((n : ℝ) ^ cA))]
    exact hsum

  have hcharge : ∀ᶠ n : ℕ in atTop,
      ∀ hG : GridFacts η n,
        (2 * sC η n + dC η n + 1 : ℝ) ^ 4 *
          (2 * Real.exp (-((n : ℝ) ^ cA))) ≤ 1 / 2 ∧
        Real.exp (-((n : ℝ) ^ cA)) < 1 / 2 := by
    filter_upwards [hChargeExp, Filter.eventually_ge_atTop (324 : ℕ)] with n hce hn324 hG
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnge : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hsle : sC η n ≤ mC η n := by
      dsimp [mC]
      calc
        sC η n = sC η n * 1 := by omega
        _ ≤ sC η n * lC n := Nat.mul_le_mul_left _ hG.pos.2.1
    have h2s : 2 * sC η n ≤ n := by
      calc
        2 * sC η n ≤ 2 * mC η n := Nat.mul_le_mul_left _ hsle
        _ ≤ n := hG.split
    have hdcast : (dC η n : ℝ) ≤ n := by simpa using hG.hd_ok.2.2
    have hdNat : dC η n ≤ n := by exact_mod_cast hdcast
    have hdimNat : 2 * sC η n + dC η n + 1 ≤ 3 * n := by omega
    have hdim : (2 * sC η n + dC η n + 1 : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast hdimNat
    have hchargeBound :
        (2 * sC η n + dC η n + 1 : ℝ) ^ 4 *
            (2 * Real.exp (-((n : ℝ) ^ cA))) ≤
          (3 * (n : ℝ)) ^ 4 * (2 * (n : ℝ) ^ (-8 : ℝ)) := by
      have hBpow :
          (2 * sC η n + dC η n + 1 : ℝ) ^ 4 ≤ (3 * (n : ℝ)) ^ 4 := by
        gcongr
      have hExp : 2 * Real.exp (-((n : ℝ) ^ cA)) ≤ 2 * (n : ℝ) ^ (-8 : ℝ) := by
        have hce' : Real.exp (-((n : ℝ) ^ cA)) ≤ (n : ℝ) ^ (-8 : ℝ) := by
          simpa [neg_one_mul] using hce
        exact mul_le_mul_of_nonneg_left hce' (by norm_num)
      calc
        _ ≤ (3 * (n : ℝ)) ^ 4 * (2 * Real.exp (-((n : ℝ) ^ cA))) :=
          mul_le_mul_of_nonneg_right hBpow (by positivity)
        _ ≤ (3 * (n : ℝ)) ^ 4 * (2 * (n : ℝ) ^ (-8 : ℝ)) :=
          mul_le_mul_of_nonneg_left hExp (by positivity)
    have hpowid : (n : ℝ) ^ 4 * (n : ℝ) ^ (-8 : ℝ) = (n : ℝ) ^ (-4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]
      congr 1
      norm_num
    have hcalc : (3 * (n : ℝ)) ^ 4 * (2 * (n : ℝ) ^ (-8 : ℝ)) =
        162 * (n : ℝ) ^ (-4 : ℝ) := by
      rw [mul_pow]
      calc
        3 ^ 4 * (n : ℝ) ^ 4 * (2 * (n : ℝ) ^ (-8 : ℝ)) =
            2 * 3 ^ 4 * ((n : ℝ) ^ 4 * (n : ℝ) ^ (-8 : ℝ)) := by ring
        _ = 162 * (n : ℝ) ^ (-4 : ℝ) := by rw [hpowid]; norm_num
    have hfinal : 162 * (n : ℝ) ^ (-4 : ℝ) ≤ 1 / 2 := by
      have hrecip : (n : ℝ) ^ (-1 : ℝ) ≤ 1 / 324 := by
        rw [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ)), Real.rpow_one]
        simpa [one_div] using
          (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 324)
            (by exact_mod_cast (show 324 ≤ n by omega)))
      have hpow4 : (n : ℝ) ^ (-4 : ℝ) ≤ (n : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnge (by norm_num)
      nlinarith [hpow4.trans hrecip]
    have hrecip324 : (n : ℝ) ^ (-1 : ℝ) ≤ 1 / 324 := by
      rw [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ)), Real.rpow_one]
      simpa [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 324)
          (by exact_mod_cast (show 324 ≤ n by omega)))
    have hpow8 : (n : ℝ) ^ (-8 : ℝ) ≤ (n : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnge (by norm_num)
    have hlast : Real.exp (-((n : ℝ) ^ cA)) < 1 / 2 := by
      exact lt_of_le_of_lt (by simpa [neg_one_mul] using hce.trans (hpow8.trans hrecip324)) (by norm_num)
    exact ⟨hchargeBound.trans (by rw [hcalc]; exact hfinal), hlast⟩

  obtain ⟨n₀₁, hn₀₁⟩ := Filter.eventually_atTop.1 hprob
  obtain ⟨n₀₂, hn₀₂⟩ := Filter.eventually_atTop.1 hcharge
  let n₀ := max n₀₁ n₀₂
  refine ⟨cA, hcA, n₀, ?_⟩
  intro D hn hG
  have hn₁ : n₀₁ ≤ D.n := le_trans (le_max_left _ _) hn
  have hn₂ : n₀₂ ≤ D.n := le_trans (le_max_right _ _) hn
  have hprobD := hn₀₁ D.n hn₁
  have hchargeD := hn₀₂ D.n hn₂ hG
  constructor
  · simpa [Ctx.eps0, Ctx.Δ] using hprobD
  · constructor
    · exact hchargeD.1
    · exact hchargeD.2

end Lane_q_s08_anchor

end HypercubeRamsey.S08

end
