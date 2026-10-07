import HypercubeRamsey.S08.L81.OddNodes

namespace HypercubeRamsey.Lane_q_s08_even

open Classical OAI.HypercubeRamsey
open HypercubeRamsey.S08
open scoped BigOperators

theorem keyDist_triangle {η₀ : ℝ} {n : ℕ} (a b c : Key η₀ n) :
    keyDist a c ≤ keyDist a b + keyDist b c := by
  unfold keyDist
  calc
    (∑ r, Nat.dist (a r).val (c r).val) ≤
        ∑ r, (Nat.dist (a r).val (b r).val + Nat.dist (b r).val (c r).val) :=
      Finset.sum_le_sum fun r _ => Nat.dist.triangle_inequality _ _ _
    _ = _ := Finset.sum_add_distrib

theorem cellDist_triangle {η₀ : ℝ} {n : ℕ} (a b c : Cell η₀ n) :
    cellDist a c ≤ cellDist a b + cellDist b c := by
  unfold cellDist
  calc
    keyDist a.1 c.1 + _ ≤
        (keyDist a.1 b.1 + keyDist b.1 c.1) +
          (_root_.hammingDist a.2 b.2 + _root_.hammingDist b.2 c.2) :=
      add_le_add (keyDist_triangle _ _ _) (_root_.hammingDist_triangle _ _ _)
    _ = _ := by ring

theorem cellDist_symm {η₀ : ℝ} {n : ℕ} (a b : Cell η₀ n) :
    cellDist a b = cellDist b a := by
  simp [cellDist, keyDist, Nat.dist_comm, _root_.hammingDist_comm]

theorem padNbr_cellDist_le_one {η₀ : ℝ} {n : ℕ} {c e : Cell η₀ n}
    (h : PadNbr c e) : cellDist c e ≤ 1 := by
  rcases h with ⟨hkey, hres⟩ | ⟨hres, hkey⟩
  · have hd : _root_.hammingDist c.2 e.2 ≤ 1 := (Finset.mem_filter.mp hres).2
    simpa [cellDist, keyDist, hkey] using hd
  · have hd : keyDist c.1 e.1 = 1 := (Finset.mem_filter.mp hkey).2
    simp [cellDist, hres, hd]

theorem presOf_eq_of_agree {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (q : D.Pre) (c : D.CellT) (W W' : D.Anch)
    (hAgree : ∀ e ∈ cellBall c 1, W e = W' e) :
    D.presOf q W c = D.presOf q W' c := by
  classical
  have hcross (u : D.CrossSub c.1) : (u.1, c.2) ∈ cellBall c 1 := by
    have hk : keyDist c.1 u.1 = 1 := (Finset.mem_filter.mp u.2).2
    have hd : cellDist c (u.1, c.2) ≤ 1 := by simp [cellDist, hk]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
  unfold Ctx.presOf
  apply Prod.ext
  · rfl
  · funext u
    have hu := hAgree (u.1, c.2) (hcross u)
    simp [hu]

theorem presValid_eq_of_agree {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (q : D.Pre) (c : D.CellT) (W W' : D.Anch)
    (hAgree : ∀ e ∈ cellBall c 1, W e = W' e) :
    D.PresValid q W c = D.PresValid q W' c := by
  have hPres := presOf_eq_of_agree D q c W W' hAgree
  unfold Ctx.PresValid
  rw [hPres]

theorem p0_eq_of_agree {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (q : D.Pre) (c : D.CellT) (W W' : D.Anch) (y : Fin D.N)
    (hAgree : ∀ e ∈ cellBall c 1, W e = W' e) :
    D.p0 q W c y = D.p0 q W' c y := by
  have hPres := presOf_eq_of_agree D q c W W' hAgree
  have hValid := presValid_eq_of_agree D q c W W' hAgree
  unfold Ctx.p0
  rw [hValid, hPres]

theorem ordHit_eq_of_agree {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (c : D.CellT) (W W' : D.Anch) (y : Fin D.N)
    (hAgree : ∀ e ∈ cellBall c 1, W e = W' e) :
    D.OrdHit W c y = D.OrdHit W' c y := by
  classical
  apply propext
  constructor
  · intro hh b hb
    have hmem : (c.1, b) ∈ cellBall c 1 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, padNbr_cellDist_le_one (Or.inl ⟨rfl, hb⟩)⟩
    have heq := hAgree (c.1, b) hmem
    simpa [Ctx.OrdHit, heq] using hh b hb
  · intro hh b hb
    have hmem : (c.1, b) ∈ cellBall c 1 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, padNbr_cellDist_le_one (Or.inl ⟨rfl, hb⟩)⟩
    have heq := hAgree (c.1, b) hmem
    simpa [Ctx.OrdHit, heq] using hh b hb

theorem ordRet_eq_of_agree {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (q : D.Pre) (c : D.CellT) (W W' : D.Anch)
    (hAgree : ∀ e ∈ cellBall c 1, W e = W' e) :
    D.ordRet q W c = D.ordRet q W' c := by
  classical
  unfold Ctx.ordRet
  apply Finset.sum_congr rfl
  intro y hy
  rw [p0_eq_of_agree D q c W W' y hAgree, ordHit_eq_of_agree D c W W' y hAgree]

theorem valid8_eq_of_agree {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (q : D.Pre) (c : D.CellT) (W W' : D.Anch)
    (hAgree : ∀ e ∈ cellBall c 1, W e = W' e) :
    D.Valid8 q W c = D.Valid8 q W' c := by
  unfold Ctx.Valid8
  rw [presValid_eq_of_agree D q c W W' hAgree, ordRet_eq_of_agree D q c W W' hAgree]

theorem prow_depends_ball_one {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (q : D.Pre) (c : D.CellT) (y : Fin D.N) :
    FinProb.DependsOn (fun W : D.Anch => D.prow q W c y) (cellBall c 1) := by
  intro W W' hAgree
  have hValid := valid8_eq_of_agree D q c W W' hAgree
  have hp0 : ∀ z, D.p0 q W c z = D.p0 q W' c z :=
    fun z => p0_eq_of_agree D q c W W' z hAgree
  have hHit : ∀ z, D.OrdHit W c z = D.OrdHit W' c z :=
    fun z => ordHit_eq_of_agree D c W W' z hAgree
  have hRet := ordRet_eq_of_agree D q c W W' hAgree
  change (if D.Valid8 q W c then
      D.p0 q W c y * (if D.OrdHit W c y then 1 else 0) / D.ordRet q W c else 0) =
    (if D.Valid8 q W' c then
      D.p0 q W' c y * (if D.OrdHit W' c y then 1 else 0) / D.ordRet q W' c else 0)
  rw [hValid, hp0 y, hHit y, hRet]

theorem refRow_depends_ball_two {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (q : D.Pre) (e c : D.CellT) (y : Fin D.N) (hd : cellDist e c ≤ 1) :
    FinProb.DependsOn (fun W : D.Anch => D.refRow q W e c y) (cellBall e 2) := by
  intro W W' hAgree
  have hLocal : ∀ d ∈ cellBall c 1, W d = W' d := by
    intro d hd'
    by_cases hde : d = e
    · subst d
      have hmem : e ∈ cellBall e 2 := by
        apply Finset.mem_filter.mpr
        simp [cellDist, keyDist]
      exact hAgree e hmem
    · have hdist := cellDist_triangle e c d
      have htwo : cellDist e d ≤ 2 := by
        have hd'val := (Finset.mem_filter.mp hd').2
        omega
      have hmem : d ∈ cellBall e 2 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, htwo⟩
      exact hAgree d hmem
  have hValid := presValid_eq_of_agree D q c W W' hLocal
  have hp0 : ∀ z, D.p0 q W c z = D.p0 q W' c z :=
    fun z => p0_eq_of_agree D q c W W' z hLocal
  simp [Ctx.refRow, hValid, hp0 y]

theorem evenStar_depends_ball_two {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (hG : GridFacts η₀ D.n) (q : D.Pre) (a : EvenRole D.n) (x : Fin D.N) :
    FinProb.DependsOn (fun W : D.Anch => D.evenStar q W a x)
      (cellBall (cellOf η₀ a.1) 2) := by
  classical
  intro W W' hAgree
  let target : D.CellT := cellOf η₀ a.1
  have hlocal (c : D.CellT) (hc : cellDist target c ≤ 1) (d : D.CellT)
      (hd : d ∈ cellBall c 1) : W d = W' d := by
    have hcd := (Finset.mem_filter.mp hd).2
    have htri := cellDist_triangle target c d
    have hdist : cellDist target d ≤ 2 := by omega
    exact hAgree d (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩)
  have hupdate (z : Fin D.N) (c : D.CellT) (hc : cellDist target c ≤ 1)
      (d : D.CellT) (hd : d ∈ cellBall c 1) :
      Function.update W target z d = Function.update W' target z d := by
    by_cases hde : d = target
    · subst d
      simp
    · rw [Function.update_of_ne hde, Function.update_of_ne hde]
      exact hlocal c hc d hd
  have hflipPad (j : Fin D.n) :
      PadNbr target (cellOf η₀ (cubeFlip a.1 j)) :=
    hG.edge a.1 (cubeFlip a.1 j) (cubeFlip_adj a.1 j)
  have hflipDist (j : Fin D.n) :
      cellDist target (cellOf η₀ (cubeFlip a.1 j)) ≤ 1 :=
    padNbr_cellDist_le_one (hflipPad j)
  have hlikEq (z : Fin D.N) (y : Fin D.n → Fin D.N) :
      D.starLik q W a.1 z y = D.starLik q W' a.1 z y := by
    unfold Ctx.starLik
    apply Finset.prod_congr rfl
    intro j hj
    exact (prow_depends_ball_one D q (cellOf η₀ (cubeFlip a.1 j)) (y j))
      (Function.update W target z) (Function.update W' target z)
      (hupdate z (cellOf η₀ (cubeFlip a.1 j)) (hflipDist j))
  have hmargEq (y : Fin D.n → Fin D.N) :
      D.starMarg q W a.1 y = D.starMarg q W' a.1 y := by
    unfold Ctx.starMarg
    apply Finset.sum_congr rfl
    intro z hz
    rw [hlikEq z y]
  have hrefEq (y : Fin D.n → Fin D.N) :
      D.starRef q W a.1 y = D.starRef q W' a.1 y := by
    unfold Ctx.starRef
    apply Finset.prod_congr rfl
    intro j hj
    exact (refRow_depends_ball_two D q target
      (cellOf η₀ (cubeFlip a.1 j)) (y j) (hflipDist j)) W W' hAgree
  have hPredEq (y : Fin D.n → Fin D.N) :
      D.PredFail q W a.1 y = D.PredFail q W' a.1 y := by
    unfold Ctx.PredFail
    rw [hmargEq y, hrefEq y]
  have hRowAtEq (y : Fin D.n → Fin D.N) :
      D.evenRowAt q W a y x = D.evenRowAt q W' a y x := by
    unfold Ctx.evenRowAt
    rw [hlikEq x y, hmargEq y]
  unfold Ctx.evenStar
  apply Finset.sum_congr rfl
  intro y hy
  have hrowProd :
      (∏ j, D.prow q W (cellOf η₀ (cubeFlip a.1 j)) (y j)) =
        ∏ j, D.prow q W' (cellOf η₀ (cubeFlip a.1 j)) (y j) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact (prow_depends_ball_one D q (cellOf η₀ (cubeFlip a.1 j)) (y j)) W W'
      (hlocal (cellOf η₀ (cubeFlip a.1 j)) (hflipDist j))
  rw [hrowProd, hPredEq y, hRowAtEq y]

theorem evenStar_nonneg {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (hP : D.PRowFacts) (q : D.Pre) (W : D.Anch) (a : EvenRole D.n) (x : Fin D.N) :
    0 ≤ D.evenStar q W a x := by
  classical
  have hLikNN (z : Fin D.N) (y : Fin D.n → Fin D.N) :
      0 ≤ D.starLik q W a.1 z y := by
    unfold Ctx.starLik
    apply Finset.prod_nonneg
    intro j hj
    exact (hP q (Function.update W (cellOf η₀ a.1) z)
      (cellOf η₀ (cubeFlip a.1 j))).1 (y j)
  have hMargNN (y : Fin D.n → Fin D.N) : 0 ≤ D.starMarg q W a.1 y := by
    unfold Ctx.starMarg
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg ((D.Usel q (cellOf η₀ a.1)).nonneg z) (hLikNN z y)
  have hRowAtNN (y : Fin D.n → Fin D.N) : 0 ≤ D.evenRowAt q W a y x := by
    unfold Ctx.evenRowAt
    exact div_nonneg
      (mul_nonneg (hLikNN x y) ((D.Usel q (cellOf η₀ a.1)).nonneg x)) (hMargNN y)
  unfold Ctx.evenStar
  apply Finset.sum_nonneg
  intro y hy
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro j hj
    exact (hP q W (cellOf η₀ (cubeFlip a.1 j))).1 (y j)
  · apply mul_nonneg
    · split_ifs <;> norm_num
    · exact mul_nonneg (Nat.cast_nonneg _) (hRowAtNN y)

theorem pi_weight_split {ι : Type*} [Fintype ι] [DecidableEq ι]
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
      (∏ i : {i // i ∉ s}, f i.1) = ∏ i : {i // i ∈ t}, f i.1 := by
        exact Fintype.prod_equiv ecomp _ _ (by intro i; rfl)
      _ = ∏ i ∈ t.attach, f i.1 := by rw [Finset.univ_eq_attach]
      _ = ∏ i ∈ t, f i := Finset.prod_attach t f
      _ = ∏ i ∈ Finset.univ with i ∉ s, f i := by simp [t]
  calc
    (∏ i, (P i).w (ω i)) = (∏ i, f i) := by rfl
    _ = (∏ i ∈ Finset.univ with i ∈ s, f i) *
        (∏ i ∈ Finset.univ with i ∉ s, f i) :=
      (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ s) f).symm
    _ = (∏ i : {i // i ∈ s}, f i.1) * (∏ i : {i // i ∉ s}, f i.1) := by
      rw [← hs, ← hnot]

theorem pi_expect_split {ι : Type*} [Fintype ι] [DecidableEq ι]
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
  rw [pi_weight_split P s (e.symm (a, b))]
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

theorem raw_evenStar_le {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (q : D.Pre) (a : EvenRole D.n) (x : Fin D.N) (hCan : D.StarCancel) :
    (D.rawAnchors q).expect (fun W => D.evenStar q W a x) ≤
      (D.N : ℝ) * (D.Usel q (cellOf η₀ a.1)).w x := by
  classical
  let c : D.CellT := cellOf η₀ a.1
  let S : Finset D.CellT := {c}
  have hc : c ∈ S := by simp [S]
  have hnonempty : Nonempty (Fin D.N) := by
    by_contra hne
    haveI : IsEmpty (Fin D.N) := ⟨fun z => hne ⟨z⟩⟩
    have hs := (D.Usel q c).sum_eq_one
    simp at hs
  let z₀ : Fin D.N := Classical.choice hnonempty
  let eSingle : Fin D.N ≃ (∀ i : {i // i ∈ S}, Fin D.N) :=
    { toFun := fun z _ => z
      invFun := fun b => b ⟨c, hc⟩
      left_inv := by intro z; rfl
      right_inv := by
        intro b
        funext i
        have hi : (i : D.CellT) = c := by
          have hmem : (i : D.CellT) ∈ ({c} : Finset D.CellT) := by simpa [S] using i.2
          exact Finset.mem_singleton.mp hmem
        apply congrArg b
        exact Subtype.ext hi.symm }
  let P : D.CellT → FinProb (Fin D.N) := fun d => D.Usel q d
  let Ps : FinProb (∀ i : {i // i ∈ S}, Fin D.N) :=
    FinProb.pi (fun i : {i // i ∈ S} => P i.1)
  let Pc : FinProb (∀ i : {i // i ∉ S}, Fin D.N) :=
    FinProb.pi (fun i : {i // i ∉ S} => P i.1)
  let e : D.Anch ≃ ((∀ i : {i // i ∈ S}, Fin D.N) ×
      (∀ i : {i // i ∉ S}, Fin D.N)) :=
    Equiv.piEquivPiSubtypeProd (fun i : D.CellT => i ∈ S) (fun _ => Fin D.N)
  have hweight (z : Fin D.N) : Ps.w (eSingle z) = (D.Usel q c).w z := by
    simp [Ps, P, FinProb.pi, eSingle, S]
  have hupdate (b : ∀ i : {i // i ∉ S}, Fin D.N) (z : Fin D.N) :
      e.symm (eSingle z, b) = Function.update (e.symm (eSingle z₀, b)) c z := by
    funext d
    by_cases hd : d = c
    · subst d
      simp [e, eSingle, S, hc, Equiv.piEquivPiSubtypeProd_symm_apply]
    · simp [e, eSingle, S, hd, Equiv.piEquivPiSubtypeProd_symm_apply]
  change (FinProb.pi P).expect (fun W => D.evenStar q W a x) ≤ _
  rw [pi_expect_split P S (fun W => D.evenStar q W a x)]
  rw [← Equiv.sum_comp eSingle (fun a' =>
    ∑ b : (∀ i : {i // i ∉ S}, Fin D.N),
      Ps.w a' * Pc.w b * D.evenStar q (e.symm (a', b)) a x)]
  calc
    (∑ z : Fin D.N, ∑ b : (∀ i : {i // i ∉ S}, Fin D.N),
        Ps.w (eSingle z) * Pc.w b * D.evenStar q (e.symm (eSingle z, b)) a x) =
        ∑ b : (∀ i : {i // i ∉ S}, Fin D.N),
          (Pc.w b) * ∑ z : Fin D.N,
            (D.Usel q c).w z * D.evenStar q
              (Function.update (e.symm (eSingle z₀, b)) c z) a x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∑ z : Fin D.N,
            Ps.w (eSingle z) * Pc.w b * D.evenStar q (e.symm (eSingle z, b)) a x) =
            ∑ z : Fin D.N,
              Pc.w b * (Ps.w (eSingle z) * D.evenStar q (e.symm (eSingle z, b)) a x) := by
                apply Finset.sum_congr rfl
                intro z hz
                ring
        _ = Pc.w b * ∑ z : Fin D.N,
              Ps.w (eSingle z) * D.evenStar q (e.symm (eSingle z, b)) a x := by
                rw [Finset.mul_sum]
        _ = Pc.w b * ∑ z : Fin D.N,
              (D.Usel q c).w z * D.evenStar q
                (Function.update (e.symm (eSingle z₀, b)) c z) a x := by
                congr 1
                apply Finset.sum_congr rfl
                intro z hz
                rw [hweight z, hupdate b z]
    _ ≤ ∑ b : (∀ i : {i // i ∉ S}, Fin D.N),
          (Pc.w b) * ((D.N : ℝ) * (D.Usel q c).w x) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hCan q (e.symm (eSingle z₀, b)) a x)
        (Pc.nonneg b)
    _ = (D.N : ℝ) * (D.Usel q c).w x := by
      rw [← Finset.sum_mul]
      simp [Pc.sum_eq_one]

theorem pi_expect_prod_of_disjoint {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (f : κ → (∀ i, Ω i) → ℝ)
    (scope : κ → Finset ι) (s : Finset κ)
    (hdep : ∀ k, k ∈ s → FinProb.DependsOn (f k) (scope k))
    (hdisj : ∀ k, k ∈ s → ∀ j, j ∈ s → k ≠ j → Disjoint (scope k) (scope j)) :
    (FinProb.pi P).expect (fun ω => ∏ k ∈ s, f k ω) =
      ∏ k ∈ s, (FinProb.pi P).expect (f k) := by
  classical
  revert hdep hdisj
  induction s using Finset.induction_on with
  | empty =>
      intro hdep hdisj
      simp only [Finset.prod_empty]
      rw [FinProb.expect_const]
  | @insert k s hk ih =>
      intro hdep hdisj
      have hdepS : ∀ j, j ∈ s → FinProb.DependsOn (f j) (scope j) := by
        intro j hj
        exact hdep j (Finset.mem_insert_of_mem hj)
      have hdisjS : ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j →
          Disjoint (scope i) (scope j) := by
        intro i hi j hj hij
        exact hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hrestDep : FinProb.DependsOn (fun ω => ∏ j ∈ s, f j ω) (s.biUnion scope) := by
        intro ω ω' hω
        apply Finset.prod_congr rfl
        intro j hj
        apply hdepS j hj
        intro i hi
        exact hω i (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩)
      have hscopeDisj : Disjoint (scope k) (s.biUnion scope) := by
        apply Finset.disjoint_left.mpr
        intro i hi hbi
        rcases Finset.mem_biUnion.mp hbi with ⟨j, hj, hij⟩
        have hkj : k ≠ j := by
          intro hEq
          subst j
          exact hk hj
        exact (Finset.disjoint_left.mp
          (hdisj k (Finset.mem_insert_self k s) j (Finset.mem_insert_of_mem hj) hkj)) hi hij
      have hfactor := FinProb.pi_expect_mul_of_disjoint P (f k)
        (fun ω => ∏ j ∈ s, f j ω) (scope k) (s.biUnion scope)
        (hdep k (Finset.mem_insert_self k s)) hrestDep hscopeDisj
      calc
        (FinProb.pi P).expect (fun ω => ∏ j ∈ insert k s, f j ω) =
            (FinProb.pi P).expect (fun ω => f k ω * ∏ j ∈ s, f j ω) := by
          congr 1
          funext ω
          rw [Finset.prod_insert hk]
        _ = (FinProb.pi P).expect (f k) *
            (FinProb.pi P).expect (fun ω => ∏ j ∈ s, f j ω) := hfactor
        _ = (FinProb.pi P).expect (f k) * ∏ j ∈ s, (FinProb.pi P).expect (f j) := by
          rw [ih hdepS hdisjS]
        _ = ∏ j ∈ insert k s, (FinProb.pi P).expect (f j) := by
          rw [Finset.prod_insert hk]

end HypercubeRamsey.Lane_q_s08_even
