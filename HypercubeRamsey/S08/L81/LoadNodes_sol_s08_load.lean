import HypercubeRamsey.S08.L81.PosteriorNodes

noncomputable section
namespace HypercubeRamsey.S08.Lane_sol_s08_load
open Classical OAI.HypercubeRamsey
open scoped BigOperators

private theorem pad_res_dist {η₀ : ℝ} {n : ℕ} {c e : Cell η₀ n}
    (hc : PadNbr c e) : _root_.hammingDist c.2 e.2 ≤ 1 := by
  rcases hc with h | h
  · exact (Finset.mem_filter.mp h.2).2
  · simp [h.1]

private theorem cand_scope {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    {P : D.Pos} {c e : D.CellT} (hce : PadNbr c e) {L : D.LList c.1}
    (hL : D.Cand P c L) :
    (∀ ℓ ∈ L.1, _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 2) ∧
    (∀ u : D.CrossSub c.1, _root_.hammingDist (L.2 u).1 e.2 ≤ rH D.n + 2) := by
  have hce' := pad_res_dist hce
  constructor
  · intro ℓ hℓ
    obtain ⟨b, hb, hdist⟩ := (hL.2.1 ℓ hℓ).2
    have hcb := (Finset.mem_filter.mp hb).2
    have hbc : _root_.hammingDist b c.2 ≤ 1 := by simpa [_root_.hammingDist_comm] using hcb
    have htri := _root_.hammingDist_triangle ℓ.1 b e.2
    have htri' := _root_.hammingDist_triangle b c.2 e.2
    omega
  · intro u
    have hdist := (hL.2.2 u).2
    have htri := _root_.hammingDist_triangle (L.2 u).1 c.2 e.2
    omega

private theorem family_local {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (Θ : D.Hist) (P P' : D.Pos) (t t' : D.Tags) (c e : D.CellT)
    (hce : PadNbr c e)
    (hEq : ∀ (g : D.KeyT) (ℓ : D.Loc), _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 2 →
      P g ℓ = P' g ℓ ∧ t g ℓ = t' g ℓ) :
    D.family Θ P t c = D.family Θ P' t' c := by
  have hCand : ∀ L, D.Cand P c L ↔ D.Cand P' c L := by
    intro L
    have forward (Q Q' : D.Pos)
        (hQ : ∀ (g : D.KeyT) (ℓ : D.Loc), _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 2 → Q g ℓ = Q' g ℓ)
        (hL : D.Cand Q c L) : D.Cand Q' c L := by
      have hscope := cand_scope D hce hL
      refine ⟨hL.1, ?_, ?_⟩
      · intro ℓ hℓ
        exact ⟨(hQ c.1 ℓ (hscope.1 ℓ hℓ)) ▸ (hL.2.1 ℓ hℓ).1,
          (hL.2.1 ℓ hℓ).2⟩
      · intro u
        exact ⟨(hQ u.1 (L.2 u) (hscope.2 u)) ▸ (hL.2.2 u).1, (hL.2.2 u).2⟩
    exact ⟨forward P P' (fun g ℓ hℓ => (hEq g ℓ hℓ).1),
      forward P' P (fun g ℓ hℓ => (hEq g ℓ hℓ).1.symm)⟩
  have hBad (L : D.LList c.1) (hL : D.Cand P c L) :
      D.BadList Θ t c L ↔ D.BadList Θ t' c L := by
    have hscope := cand_scope D hce hL
    have hInt : D.listInt t c.1 L = D.listInt t' c.1 L := by
      funext ℓ
      by_cases hℓ : ℓ ∈ L.1
      · simp only [Ctx.listInt, hℓ, ite_true]
        rw [(hEq c.1 ℓ (hscope.1 ℓ hℓ)).2]
      · simp [Ctx.listInt, hℓ]
    have hCross : D.listCrossTag t c.1 L = D.listCrossTag t' c.1 L := by
      funext u
      exact (hEq u.1 (L.2 u) (hscope.2 u)).2
    simp only [Ctx.BadList, hInt, hCross]
  have hpred : (fun L : D.LList c.1 => decide (D.Cand P c L ∧ D.BadList Θ t c L)) =
      (fun L : D.LList c.1 => decide (D.Cand P' c L ∧ D.BadList Θ t' c L)) := by
    funext L
    by_cases hL : D.Cand P c L
    · simp only [hL, (hCand L).mp hL, true_and, hBad L hL]
    · simp [hL, ← hCand L]
  unfold Ctx.family
  rw [hpred]

private theorem elig_local {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (Θ : D.Hist) (P P' : D.Pos) (t t' : D.Tags) (e : D.CellT)
    (hEq : ∀ (g : D.KeyT) (ℓ : D.Loc), _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 →
      P g ℓ = P' g ℓ ∧ t g ℓ = t' g ℓ)
    (b : D.ResT) (hb : _root_.hammingDist b e.2 ≤ 4 * HH η₀ D.n)
    (j : Fin (HH η₀ D.n + 1)) :
    D.elig Θ P t e.1 b j = D.elig Θ P' t' e.1 b j := by
  have hsmall (g : D.KeyT) (ℓ : D.Loc) (hℓ : _root_.hammingDist ℓ.1 b ≤ rH D.n + 2) :
      P g ℓ = P' g ℓ ∧ t g ℓ = t' g ℓ := by
    apply hEq
    have htri := _root_.hammingDist_triangle ℓ.1 b e.2
    omega
  have hforbid (ℓ : D.Loc) :
      D.Forbidden Θ P t (e.1, b) ℓ ↔ D.Forbidden Θ P' t' (e.1, b) ℓ := by
    unfold Ctx.Forbidden
    apply exists_congr
    intro c
    apply and_congr_right
    intro hce
    rw [family_local D Θ P P' t t' c (e.1, b) hce hsmall]
  apply Finset.ext
  intro ℓ
  simp only [Ctx.elig, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hdist : _root_.hammingDist ℓ.1 b ≤ rH D.n
  · rw [(hsmall e.1 ℓ (by omega)).1, hforbid]
  · simp [hdist]

 theorem legal_local {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (Θ : D.Hist) (P P' : D.Pos) (t t' : D.Tags) (e : D.CellT)
    (hEq : ∀ (g : D.KeyT) (ℓ : D.Loc), _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 →
      P g ℓ = P' g ℓ ∧ t g ℓ = t' g ℓ) :
    D.LocalLegal Θ P t e ↔ D.LocalLegal Θ P' t' e := by
  have forward (Q Q' : D.Pos) (v v' : D.Tags)
      (hQ : ∀ (g : D.KeyT) (ℓ : D.Loc), _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 4 * HH η₀ D.n + 2 →
        Q g ℓ = Q' g ℓ ∧ v g ℓ = v' g ℓ)
      (hL : D.LocalLegal Θ Q v e) : D.LocalLegal Θ Q' v' e := by
    intro b hb j
    have hb' : _root_.hammingDist b e.2 ≤ 4 * HH η₀ D.n := by
      simpa [HDParams.domBall, HDParams.Rlong, hdP] using (Finset.mem_filter.mp hb).2
    have hE := elig_local D Θ Q Q' v v' e hQ b hb' j
    have hLj := hL b hb j
    change _ ∧ _
    constructor
    · intro ℓ hℓ
      exact ⟨(Finset.mem_filter.mp hℓ).2.1,
        (Finset.mem_filter.mp hℓ).2.2.1,
        (Finset.mem_filter.mp hℓ).2.2.2.1⟩
    · simpa only [← hE] using hLj.2
  exact ⟨forward P P' t t' hEq,
    forward P' P t' t (fun g ℓ hℓ => ⟨(hEq g ℓ hℓ).1.symm, (hEq g ℓ hℓ).2.symm⟩)⟩

private theorem pi_factor {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] {Ω : V → Type*} [∀ v, Fintype (Ω v)]
    (P : ∀ v, FinProb (Ω v)) (s : Finset I)
    (f : I → (∀ v, Ω v) → ℝ) (S : I → Finset V)
    (hdep : ∀ i, FinProb.DependsOn (f i) (S i))
    (hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    (FinProb.pi P).expect (fun ω => ∏ i ∈ s, f i ω) =
      ∏ i ∈ s, (FinProb.pi P).expect (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [FinProb.expect_const]
  | @insert i s hi ih =>
      let U : Finset V := s.biUnion S
      let F : (∀ v, Ω v) → ℝ := fun ω => ∏ j ∈ s, f j ω
      have hFdep : FinProb.DependsOn F U := by
        intro ω ω' hEq
        apply Finset.prod_congr rfl
        intro j hj
        apply hdep j
        intro v hv
        exact hEq v (Finset.mem_biUnion.mpr ⟨j, hj, hv⟩)
      have hUF : Disjoint U (S i) := by
        apply Finset.disjoint_left.mpr
        intro v hvU hvI
        obtain ⟨j, hj, hv⟩ := Finset.mem_biUnion.mp hvU
        exact (Finset.disjoint_left.mp (hdis j i (by intro he; subst j; exact hi hj))) hv hvI
      have hfac := FinProb.pi_expect_mul_of_disjoint P F (f i) U (S i)
        hFdep (hdep i) hUF
      calc
        (FinProb.pi P).expect (fun ω => ∏ j ∈ insert i s, f j ω) =
            (FinProb.pi P).expect (fun ω => F ω * f i ω) := by
          congr 1
          funext ω
          simp [F, hi, Finset.prod_insert, mul_comm]
        _ = (FinProb.pi P).expect F * (FinProb.pi P).expect (f i) := hfac
        _ = (∏ j ∈ s, (FinProb.pi P).expect (f j)) * (FinProb.pi P).expect (f i) := by
          rw [ih]
        _ = ∏ j ∈ insert i s, (FinProb.pi P).expect (f j) := by
          simp [hi, Finset.prod_insert, mul_comm]

section Packing
variable {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)

private abbrev Input := Bool × ((D.M.ι × Bool) × (hdP η₀ D.n).TiePerm)
private abbrev Index := D.KeyT × D.Loc
private def inputEquiv : (D.Pos × D.TAT) ≃ (Index D → Input D) where
  toFun z k := (z.1 k.1 k.2, ((z.2.1.1 k.1 k.2, z.2.1.2 k.1 k.2), z.2.2 k.1 k.2))
  invFun w := (fun g ℓ => (w (g, ℓ)).1,
    ((fun g ℓ => (w (g, ℓ)).2.1.1, fun g ℓ => (w (g, ℓ)).2.1.2),
      fun g ℓ => (w (g, ℓ)).2.2))
  left_inv _z := rfl
  right_inv _w := rfl

private def inputLaw (Θ : D.Hist) (k : Index D) : FinProb (Input D) :=
  let p₀ := hdP η₀ D.n
  (FinProb.bernoulli (p₀.lam / (p₀.V : ℝ))).prod
    (((D.tilt Θ k.1).prod (FinProb.bernoulli ((D.n : ℝ) ^ p₀.b₀ / p₀.lam))).prod
      (FinProb.uniformAll ⟨1⟩))

private theorem input_weight (Θ : D.Hist) (w : Index D → Input D) :
    (FinProb.prod D.posLaw (D.rawTAT Θ)).w ((inputEquiv D).symm w) =
      (FinProb.pi (inputLaw D Θ)).w w := by
  simp [inputLaw, inputEquiv, Ctx.posLaw, Ctx.rawTAT, Ctx.tagLawAll,
    Ctx.actLaw, Ctx.tieLaw, HDParams.posLaw, HDParams.actLaw, HDParams.tieLaw,
    FinProb.prod, FinProb.pi, Fintype.prod_prod_type, Finset.prod_mul_distrib, mul_assoc]

private theorem input_expect (Θ : D.Hist) (f : D.Pos × D.TAT → ℝ) :
    (FinProb.prod D.posLaw (D.rawTAT Θ)).expect f =
      (FinProb.pi (inputLaw D Θ)).expect (fun w => f ((inputEquiv D).symm w)) := by
  unfold FinProb.expect
  rw [← Equiv.sum_comp (inputEquiv D).symm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [input_weight]

 theorem center_factor (Θ : D.Hist) {m : ℕ} (s : Fin m → EvenRole D.n)
    (hsep : ∀ i j : Fin m, j < i → s i ∉ evenResNear η₀
      (2 * rH D.n + 8 * HH η₀ D.n + 4) (s j))
    (f : Fin m → D.Pos × D.TAT → ℝ)
    (hdep : ∀ (i : Fin m) (z z' : D.Pos × D.TAT),
      (∀ (g : D.KeyT) (ℓ : D.Loc), _root_.hammingDist ℓ.1 (resOf η₀ (s i).1) ≤ rH D.n + 4 * HH η₀ D.n + 2 →
        z.1 g ℓ = z'.1 g ℓ ∧ z.2.1.1 g ℓ = z'.2.1.1 g ℓ ∧
        z.2.1.2 g ℓ = z'.2.1.2 g ℓ ∧ z.2.2 g ℓ = z'.2.2 g ℓ) →
      f i z = f i z') :
    (FinProb.prod D.posLaw (D.rawTAT Θ)).expect (fun z => ∏ i, f i z) =
      ∏ i, (FinProb.prod D.posLaw (D.rawTAT Θ)).expect (f i) := by
  let S : Fin m → Finset (Index D) := fun i => Finset.univ.filter fun k =>
    _root_.hammingDist k.2.1 (resOf η₀ (s i).1) ≤ rH D.n + 4 * HH η₀ D.n + 2
  let F : Fin m → (Index D → Input D) → ℝ := fun i w => f i ((inputEquiv D).symm w)
  have hF : ∀ i, FinProb.DependsOn (F i) (S i) := by
    intro i w w' hw
    apply hdep i
    intro g ℓ hℓ
    have heq := hw (g, ℓ) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓ⟩)
    exact ⟨congrArg Prod.fst heq, congrArg (fun v : Input D => v.2.1.1) heq,
      congrArg (fun v : Input D => v.2.1.2) heq, congrArg (fun v : Input D => v.2.2) heq⟩
  have hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    have hi := (Finset.mem_filter.mp hki).2
    have hj := (Finset.mem_filter.mp hkj).2
    have htri := _root_.hammingDist_triangle_left (resOf η₀ (s i).1) (resOf η₀ (s j).1) k.2.1
    have hd : _root_.hammingDist (resOf η₀ (s i).1) (resOf η₀ (s j).1) ≤
        2 * rH D.n + 8 * HH η₀ D.n + 4 := by omega
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hmem : s j ∈ evenResNear η₀ (2 * rH D.n + 8 * HH η₀ D.n + 4) (s i) := by
        simp only [evenResNear, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [_root_.hammingDist_comm] using hd
      exact hsep j i hij hmem
    · exact hsep i j hji (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
  rw [input_expect]
  change (FinProb.pi (inputLaw D Θ)).expect (fun w => ∏ i, F i w) = _
  rw [pi_factor (inputLaw D Θ) Finset.univ F S hF hdis]
  apply Finset.prod_congr rfl
  intro i hi
  exact (input_expect D Θ (f i)).symm

end Packing

end HypercubeRamsey.S08.Lane_sol_s08_load
